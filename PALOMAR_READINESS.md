# Verification and venue-readiness dossier (23 November 2026)

**Status: PREPARATION, NOT SUBMITTED.** This is publication and verification engineering for an already-public preprint, not a new mathematical theorem, new proof, external registration, endorsement, or fresh Lean compilation.

**Work of record:** [Hexagon hexagon:2610.00457v1](https://hexagonmath.org/2610.00457v1), [immutable GitHub v1.0.0 PDF](https://github.com/jjtripodo-lgtm/sparse-projective-plane-determinants/blob/3e247aa28d47cb40f252f22df3db143d0bc8ceac/paper.pdf), [reader guide](READER_GUIDE.md), [ORCID](https://orcid.org/0009-0006-9180-4953). The Zenodo deposit was withdrawn on 22 October 2026 and is not a live DOI. Hexagon has assigned no DOI and is not peer review.

## Already established and exact proposed delta

The **existing public package** includes 98 mathematical Lean modules, source/hash checkers, archived execution evidence and an exact written scalar certificate. The public release audit [did not execute a fresh Lean build](FORMAL_SCOPE.md). The frozen mathematical sources and historical receipts remain unchanged.

Source entrypoints for the already-existing theorem are:

- companion/SparseComponent/TotalFamily/FullFamily.lean, declarations determinant_total_family, determinant_total_family_budget, determinant_total_family_equality_iff, determinant_total_family_budget_equality_iff and literal_total_family.
- companion/SparseComponent/TotalFamily/RealEntryTransfer.lean, literal_real_total_family and equality transfer for literal real zero-one entries.
- companion/SparseComponent/TotalFamily/OrderObstruction.lean, determinant_family_strict_of_order_not_dvd for forbidden orders.

Scope: densities **r=3 through 14**, arbitrary natural matrix order, a global total-ones budget (not per-row or per-column degree restrictions), and projective-plane-block equality conditions with external plane-existence questions distinguished. This package does **not** prove density 15 or an all-density theorem.

The **proposed delta** is independent public mechanical checking of a small, auditable Challenge/Solution pair backed by a ported proof closure. That would be an additional *formal verification registration*, not discovery or independent human proof review. Scientific novelty: **NOT ASSESSED** in this dossier.

## Concrete Palomar blockers

Policy sources, accessed 23 November 2026: [how to submit](https://palomar-registry.org/how-to-submit), [current template](https://github.com/PalomarRegistry/PalomarTemplate), [submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md). Re-read the policy before preparing a final submission.

1. **Unsupported frozen toolchain:** companion/lean-toolchain is **leanprover/lean4:v4.31.0-rc1**. Palomar's current template requires bundled Comparator at **v4.35.0-rc2 or later**. Changing a pin alone is not proof portability; an independently validated port is needed.
2. **Missing intake files:** this export has no Palomar Challenge.lean, Solution.lean, comparator.json or formalization.yaml. The Challenge must describe the original theorem independently, not hide new conditions or opaque definitions.
3. **Lean module format:** sampled source files start with import instead of module. Palomar requires every checked-in Lean source to have a module header and at most 10,000 lines, with Challenge limited to 1,000 lines/100 KiB. A complete local checkout is required to enumerate all failures.
4. **Comparison unperformed:** the exported Lean sources have not been ported to a compatible toolchain or run against Palomar's bundled Comparator, allowed-axiom and independent-kernel workflow. Historical axioms/build receipts are not a Palomar PASS.
5. **Metadata/rights:** formalization.yaml must correctly disclose authorship, AI use, limitations, prior formalizations, classifications, review state and sources. The repository-root licence covers both CC BY 4.0 manuscript text and MIT code; the formalization's declared code licence must agree with that scope.
6. **User-controlled outside registration:** Palomar requires an immutable public 40-character Git commit, a submitted Comparator path and maintainer authorization. No submission or external communication is performed by this file.

## Local checks and their limits

From a **complete checkout**, run:

    python3 palomar_preflight.py --repo . --project companion
    python3 -m unittest discover -s tests -p 'test_palomar_preflight.py' -v

The preflight returns nonzero on structural blockers. Option --expect-blocked allows testing the deliberately noncompliant frozen export without pretending it passed. Even a future STATIC_READY_ONLY means **only** that selected structural conditions look satisfied. The script does not run Lean, parse the complete YAML schema, run Comparator or independent kernels, verify formal-to-informal fidelity, obtain a human review, or assess priority. Its unit tests use synthetic local fixtures, not the mathematical source package. The original release manifest remains the authority for frozen-file integrity.

## Bounded execution sequence

1. Keep the original frozen Lean source, PDF and receipts untouched. Prepare a separate port with exact old/new file mapping.
2. Start with an independently understandable Mathlib-based Challenge expressing **the full global-budget inequality for r=3..14** and explicit scalar constants. Bridge the ported Solution to the actual prior theorem without weakening quantifiers, substituting a small case, or importing private statement definitions into Challenge.
3. Add equality as a separately named comparison only after the main bound; preserve the exact external plane-existence caveat.
4. Port the entire necessary proof closure to a supported Lean/Mathlib pair, add module headers, run a fresh project build, Comparator and allowed-axiom checks, then record source-specific receipts. Failed portability is a technical blocker, not a mathematical refutation.
5. With distinct authorization, consider [Palomar](https://submit.palomar-registry.org/) for mechanical registration; [ProofForum](https://www.proofforum.org/) for an exact-version Hexagon human-verification request; and [Proof Commons](https://proofcommons.org/) for human-reviewed statement collaboration. None guarantees human verification, and Proof Commons is not a whole-manuscript journal.

**No outside contact, new venue submission, registration, license change, published theorem edit or paid CI is authorized by this dossier.** AI assistance and the lack of independent specialist review are maintained as explicit facts.
