# Sparse determinant bounds: source companion

This companion supports *Projective-plane determinant bounds for sparse binary matrices* by John Tripodo. It contains the exact 98-module mathematical source closure for densities 3 through 14, including equality, literal real entries and the order obstruction. Density 16 is a separate result and is not part of this bundle. No statement for density 15 or all densities follows.

## Exact source verification

Requirements: Python 3.10 or later. From this directory:

```sh
python3 check_publication_sources.py --root . --manifest MAIN_RELEASE_SOURCE_MANIFEST.json
python3 -O check_publication_sources.py --root . --manifest MAIN_RELEASE_SOURCE_MANIFEST.json
python3 test_publication_checkers.py
```

The source manifest binds 122 source/configuration/audit inputs and provides the topological order of all 98 owned mathematics modules. The checker verifies hashes, import closure and forbidden proof-escape tokens. This is not compilation. The ten controls include intentionally wrong hashes and proof escapes; rejection is required.

## Fresh Lean project replay

Use Lean 4.31.0-rc1, compiler commit `fd009949156901e6cf15b6d9bf1122294b8e697a`, and mathlib `0ed37c9258f123a2c76a2175596f75c2bd50f941`. `lake-manifest.json` pins the transitive packages. Do not run an update that changes those pins. Obtain the official pinned mathlib cache in a separate checkout, then run:

```sh
python3 -O verify_publication_main.py \
  --root "$PWD" --manifest MAIN_RELEASE_SOURCE_MANIFEST.json \
  --lean /path/to/pinned/lean --mathlib /path/to/pinned/mathlib \
  --build /path/to/new-build --output /path/to/new-receipts --memory 4096
```

The build and output directories must not already exist. The driver compiles all 98 owned mathematics modules from source, runs three proof-body audits, and checks the three final interfaces at trust level zero. External mathlib objects are reused and hashed; this is not a fresh rebuild of all mathlib. It makes no network or publication requests. Allow at least 5 GiB free RAM plus space for the toolchain and mathlib.

## Written scalar certificate

The written proof's exact-integer certificate differs from the formal scalar route. It covers densities 3 through 14 and includes three deliberately invalid configurations that must fail certification. From `scalar/`:

```sh
python3 verify_family_exact.py --output result.json
python3 -O verify_family_exact.py --output result-O.json
cmp result.json result-O.json
cmp result.json certificates/exact_family.json
python3 validation/check_exact_checker.py verify_family_exact.py
```

The primary checker uses standard Python exact integer arithmetic. The independent symbolic/interval checker additionally requires SymPy. The archived outward-rounded alternative under `validation/` uses mpmath; its source and recorded outputs are supplied separately, not as a premise of Lean. A finite scalar certificate does not replace the proof of its coverage of unbounded matrix order and degree tails.

## Statement boundary

The final matrix hypotheses are actual zero-one entries and the specified total-entry budget; no row/column cap or externally supplied scalar certificate is assumed by the concrete endpoints. External projective-plane existence/nonexistence results are not formalized. An axiom audit does not establish novelty or replace reading the encoded statement. The recorded exact sources remain unchanged from the pinned mathematical snapshot; newly assembling this bundle is not itself a new Lean execution.
