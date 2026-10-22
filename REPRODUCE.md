# Reproduction

From the root of a freshly extracted export:

```sh
python3 verify_package.py
mkdir -p .reproduce
python3 build_paper.py
```

The build writes .reproduce/manuscript/paper.pdf and preserves the frozen paper.pdf. With the same TeX Live 2023 installation and fonts used in this audit, byte-identical output was checked from a second standalone copy. Across TeX installations typography and PDF bytes may differ; inspect the full output and the recorded tool version. No shell escape is enabled.

The proof-critical scalar check uses Python 3.10 or later and the standard library:

```sh
cd companion/scalar
python3 verify_family_exact.py --output ../../.reproduce/exact.json
python3 -O verify_family_exact.py --output ../../.reproduce/exact-O.json
cmp ../../.reproduce/exact.json ../../.reproduce/exact-O.json
cmp ../../.reproduce/exact.json certificates/exact_family.json
cd ../..
python3 companion/check_publication_sources.py --root companion --manifest companion/MAIN_RELEASE_SOURCE_MANIFEST.json
python3 companion/test_publication_checkers.py
```

The optional independent symbolic/enclosure check requires `sympy==1.14.0` (with `mpmath==1.3.0`). Run:

```sh
python3 companion/scalar/validation/check_exact_checker.py companion/scalar/verify_family_exact.py
```

It derives the edge polynomial from the vertex deficit, checks exact interval operations against rational fractions, and checks all anchor tangencies. The alternative outward-rounded checker and exact finite-field plane witnesses are in `companion/scalar/validation/`.

For a fresh Lean build, use exactly the toolchain and all package commits in DEPENDENCIES.json; do not update Lake pins. Follow companion/README.md. The driver compiles all 98 owned mathematics modules and audits the endpoints while reusing separately obtained, hashed mathlib dependencies. That is distinct from rebuilding mathlib from source. This release audit checked the closure and source hashes; no fresh Lean execution was available in the audit environment.
