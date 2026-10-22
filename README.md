# Projective-plane determinant bounds for sparse binary matrices

John Tripodo | [ORCID](https://orcid.org/0009-0006-9180-4953) | manuscript version 1.0.0

For each integer 3 <= r <= 14, set v=r^2-r+1 and D_r=r(r-1)^((v-1)/2). If an n by n zero-one matrix has e <= r n ones, then |det A| <= D_r^(n/v). The manuscript proves a stronger all-count inequality and characterizes equality by actual projective-plane blocks.

Read [paper.pdf](paper.pdf), [TeX source](paper.tex), and [REPRODUCE.md](REPRODUCE.md).

The selected paper covers densities 3 through 14. Density 16 is a separate result. Density 15 and a universal all-density theorem are not proved here. Plane existence/nonexistence inputs in the corollary are external cited results.

## Publication and repository

The paper is published on [Zenodo](https://zenodo.org/records/23550379), DOI [10.5281/zenodo.23550379](https://doi.org/10.5281/zenodo.23550379).

The dedicated public repository is [jjtripodo-lgtm/sparse-projective-plane-determinants](https://github.com/jjtripodo-lgtm/sparse-projective-plane-determinants). Consult VERSION.json for publication status.

Hexagon submission `2610.00457v1` is awaiting moderation and is not yet public. The Zenodo DOI above is the published citation.

The manuscript is licensed under CC BY 4.0 and original code under MIT. Read LICENSE for scope and THIRD_PARTY_NOTICES.md for retained third-party rights.

Citation metadata is in CITATION.cff and citation.bib. John Tripodo is the sole named author. His ORCID is supplied above. AI assistance is disclosed in the paper and AI_ASSISTANCE.md.

Run `python3 verify_package.py` to validate the frozen contents. That command checks files and hashes; it does not certify a proof or authorize publication. See THIRD_PARTY_NOTICES.md for source/dependency attribution.
