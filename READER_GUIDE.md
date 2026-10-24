# Reader and review guide: projective-plane determinant bounds

**John Tripodo** · [ORCID 0009-0006-9180-4953](https://orcid.org/0009-0006-9180-4953)

## Publication and citation

- [*Projective-plane determinant bounds for sparse binary matrices*, Hexagon preprint **hexagon:2610.00457v1**](https://hexagonmath.org/2610.00457v1). Hexagon is a moderated preprint repository, **not** independent peer review and **not** a DOI.
- [Immutable GitHub PDF, manuscript version 1.0.0](https://github.com/jjtripodo-lgtm/sparse-projective-plane-determinants/blob/3e247aa28d47cb40f252f22df3db143d0bc8ceac/paper.pdf) · [TeX](paper.tex) · [citation metadata](CITATION.cff). The pinned PDF is the exact GitHub reading copy; a byte-for-byte comparison with the Hexagon-hosted PDF has not been established.
- The original Zenodo deposit was **withdrawn** on 22 October 2026. DOI 10.5281/zenodo.23550379 is retained only for historical provenance. See [publication history](publication_history/README.md).

## Main mathematical claim

For each integer density `3 <= r <= 14`, define

`v = r^2 - r + 1`, `D_r = r (r-1)^((v-1)/2)`.

For an `n x n` zero-one matrix `A` with **at most** `r*n` entries equal to one, the manuscript establishes

`|det A| <= D_r^(n/v)`.

Individual row and column degrees need **not** be bounded by r. The proof gives a stronger all-count inequality and characterizes equality using direct sums of incidence matrices of projective planes of order `r-1`, when such planes exist. Claims in this manuscript are restricted to densities **3 through 14**. Density 16 belongs to a separate project; density 15 and a universal all-density result are not established here.

## What the evidence does, and does not, establish

The [reproduction guide](REPRODUCE.md) describes an exact scalar certificate, independent-style symbolic/enclosure tests and pinned formalization sources. The accompanying package includes a **98-module Lean mathematics closure**. The release audit checked source identities and closure; **a fresh Lean execution was not performed** in that audit. Exact finite certificate checks support their precisely encoded inequalities; they are not, alone, an independent specialist audit of the unbounded theorem, the mathematical encoding, or novelty.

## Modest, useful independent review tasks

Someone can usefully examine just one of these components:

1. Independently run the standard-library exact scalar checker and compare the reconstructed certificate to its committed JSON, following [REPRODUCE.md](REPRODUCE.md).
2. Review how the scalar inequality and rigorously bounded degree tails imply the **all-count** bound before specializing to total ones `e <= r*n`.
3. Check the equality characterization, including the plane-existence qualifications and the distinction between a **global entry budget** and per-row/per-column constraints.
4. Rebuild the pinned Lean companion with its unchanged dependency versions and audit the theorem statements actually discharged, independently of a prior execution receipt.

A precise counterexample or flaw report is valuable. AI assistance is explicitly disclosed; no independent human proof review, journal acceptance, or priority certification is asserted.

## Other public papers

- [Separated distances in fixed dimension](https://github.com/jjtripodo-lgtm/erdos-670-fixed-dimension)
- [Asymptotically optimal degree for the double Hall property](https://github.com/jjtripodo-lgtm/double-hall-optimal-degree)
