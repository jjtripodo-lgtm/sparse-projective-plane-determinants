#!/usr/bin/env python3
"""Fail-closed structural screen for a proposed Palomar submission.

This is NOT a Lean build, Comparator check, editorial review, or eligibility
certificate. The policy URL and observed threshold belong in the accompanying
readiness document; update both if the registry changes its specification.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

MINIMUM_TOOLCHAIN = (4, 35, 0, 2)  # 4.35.0-rc2; final is later than its RCs.
ALLOWED_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
CONFIG_KEYS = {
    "challenge_module", "solution_module", "theorem_names",
    "permitted_axioms", "definition_names", "enable_nanoda",
}


def toolchain_key(s: str) -> tuple[int, int, int, int] | None:
    match = re.fullmatch(r"leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?", s.strip())
    if not match:
        return None
    major, minor, patch = (int(match.group(i)) for i in (1, 2, 3))
    return major, minor, patch, int(match.group(4)) if match.group(4) else 999999


def physical_lines(data: bytes) -> int:
    return data.count(b"\n") + int(bool(data) and not data.endswith(b"\n"))


def module_header(data: bytes) -> bool:
    # Conservative structural hint only. Lean, not this regex, decides syntax.
    start = data[:4096].decode("utf-8-sig", errors="replace")
    return bool(re.search(r"(?m)^\s*module(?:\s|$)", start))


def inspect(repo: Path, project: str = "companion", config: str = "comparator.json") -> dict:
    repo = repo.resolve()
    issues: list[str] = []
    warnings: list[str] = []
    if not repo.is_dir():
        return {"status": "BLOCKED", "blockers": ["repository directory is missing"],
                "warnings": [], "mechanical_verification": "NOT_RUN",
                "editorial_review": "NOT_RUN", "novelty_assessment": "NOT_RUN"}
    candidate = repo / project
    if not candidate.is_dir() or not candidate.resolve().is_relative_to(repo):
        issues.append("project directory is missing or escapes the repository")
        candidate = repo
    if not any((repo / name).is_file() for name in
               ("LICENSE", "LICENSE.md", "LICENCE", "COPYING", "COPYING.md")):
        issues.append("repository-root licence missing")
    lakefiles = [f for f in ("lakefile.toml", "lakefile.lean") if (candidate / f).is_file()]
    if len(lakefiles) != 1:
        issues.append("project must contain exactly one of lakefile.toml or lakefile.lean")
    if not (candidate / "lake-manifest.json").is_file():
        warnings.append("committed Lake manifest missing; required for lakefile.lean and most dependency layouts")
    toolchain = next((p for p in (candidate / "lean-toolchain", repo / "lean-toolchain") if p.is_file()), None)
    toolchain_text = toolchain.read_text(encoding="utf-8").strip() if toolchain else None
    key = toolchain_key(toolchain_text) if toolchain_text else None
    if key is None:
        issues.append("missing or unrecognized pinned Lean toolchain")
    elif key < MINIMUM_TOOLCHAIN:
        issues.append(f"Lean {toolchain_text} predates bundled Comparator (minimum v4.35.0-rc2)")
    if not (candidate / "formalization.yaml").is_file():
        issues.append("formalization.yaml missing")
    else:
        warnings.append("formalization.yaml full schema, authorship and fidelity not validated here")

    comparator = candidate / config
    if not comparator.is_file():
        issues.append(f"Comparator configuration missing: {config}")
    else:
        try:
            if comparator.stat().st_size > 1024 * 1024:
                issues.append("Comparator configuration exceeds 1 MiB")
            cfg = json.loads(comparator.read_text(encoding="utf-8"))
            if not isinstance(cfg, dict):
                raise ValueError("not a JSON object")
            if set(cfg) - CONFIG_KEYS:
                issues.append("Comparator contains unknown keys")
            modules = []
            for keyname in ("challenge_module", "solution_module"):
                v = cfg.get(keyname)
                if not isinstance(v, str) or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9']*(?:\.[A-Za-z_][A-Za-z_0-9']*)*", v):
                    issues.append(f"invalid Comparator {keyname}")
                else:
                    modules.append(v)
                    source = candidate / (v.replace(".", "/") + ".lean")
                    if not source.is_file():
                        issues.append(f"Comparator module source missing: {source.relative_to(repo)}")
            if len(modules) == 2 and modules[0] == modules[1]:
                issues.append("Challenge and Solution must be distinct modules")
            names = cfg.get("theorem_names")
            if not isinstance(names, list) or not names or any(not isinstance(v, str) or not v for v in names):
                issues.append("Comparator theorem_names must be a nonempty string list")
            axioms = cfg.get("permitted_axioms")
            if not isinstance(axioms, list) or not all(isinstance(x, str) for x in axioms) or set(axioms) - ALLOWED_AXIOMS:
                issues.append("Comparator permitted_axioms invalid")
            defs = cfg.get("definition_names", [])
            if not isinstance(defs, list) or any(not isinstance(x, str) or not x for x in defs):
                issues.append("Comparator definition_names invalid")
            if len(modules) == 2:
                challenge = candidate / (modules[0].replace(".", "/") + ".lean")
                if challenge.is_file():
                    data = challenge.read_bytes()
                    lines = physical_lines(data)
                    if len(data) > 100 * 1024 or lines > 1000:
                        issues.append(f"Challenge exceeds 100 KiB / 1000 lines: {lines} lines, {len(data)} bytes")
                    if len(data) > 32 * 1024 or lines > 300:
                        warnings.append("Challenge exceeds preferred 32 KiB / 300 lines")
        except (ValueError, UnicodeError) as exc:
            issues.append(f"Comparator configuration invalid JSON: {exc}")

    lean_count = 0
    missing_headers: list[str] = []
    too_long: list[str] = []
    symlinks: list[str] = []
    size = 0
    for item in repo.rglob("*"):
        rel = item.relative_to(repo)
        if any(part in (".git", ".lake", ".reproduce", "__pycache__") for part in rel.parts):
            continue
        if item.is_symlink():
            if item.suffix == ".lean":
                symlinks.append(rel.as_posix())
            continue
        if not item.is_file():
            continue
        size += item.stat().st_size
        if item.suffix != ".lean":
            continue
        lean_count += 1
        data = item.read_bytes()
        if not module_header(data):
            missing_headers.append(rel.as_posix())
        if physical_lines(data) > 10000:
            too_long.append(rel.as_posix())
    if missing_headers:
        issues.append(f"{len(missing_headers)} Lean files lack a detected module header")
    if too_long:
        issues.append(f"{len(too_long)} Lean files exceed 10000 lines")
    if symlinks:
        issues.append(f"{len(symlinks)} Lean symlinks are disallowed")
    if size > 500 * 1024 * 1024:
        issues.append("repository payload exceeds 500 MiB")
    warnings.append("static checks do not run Lean, Comparator, kernel replay, or proof-fidelity review")
    return {"status": "BLOCKED" if issues else "STATIC_READY_ONLY",
            "project": project, "lean_toolchain": toolchain_text,
            "lean_files_scanned": lean_count, "missing_module_headers_count": len(missing_headers),
            "missing_module_headers_examples": missing_headers[:10],
            "oversize_lean_files": too_long[:10], "lean_symlinks": symlinks[:10],
            "repository_bytes_excluding_build_cache": size,
            "blockers": issues, "warnings": warnings,
            "mechanical_verification": "NOT_RUN", "editorial_review": "NOT_RUN",
            "human_specialist_review": "NOT_RUN", "novelty_assessment": "NOT_RUN"}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", type=Path, default=Path(__file__).resolve().parent)
    parser.add_argument("--project", default="companion")
    parser.add_argument("--comparator", default="comparator.json")
    parser.add_argument("--expect-blocked", action="store_true", help="For regression tests on a known-incomplete export")
    args = parser.parse_args()
    result = inspect(args.repo, args.project, args.comparator)
    print(json.dumps(result, indent=2, sort_keys=True))
    if args.expect_blocked:
        return 0 if result["status"] == "BLOCKED" else 1
    return 0 if result["status"] == "STATIC_READY_ONLY" else 1


if __name__ == "__main__":
    sys.exit(main())
