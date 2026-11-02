# Mathematical inputs and certificates

The completed Lean proof uses `q5-projected-certificates.tar.gz` (313,094 bytes),
containing 279 certificates with 499,829 instructions. Its SHA-256 is:

```text
e7b40f79831b5e0a44b374397d90bc4068f43d07e4226e1a45a829fd5b900e4a
```

`q5-projected-root-cases.txt` specifies the problems. The fixed manifest
`q5-projected-root-manifest.json` maps their local indices to the original
case IDs, records individual proof hashes, and supplies two zero-budget
counterexamples explaining the exceptional budget-one cases. Its entries
are proof inputs, not a mutable validation log. The separate audit
`scripts/check_five_colour_root_projection.py` checks all transformations,
physical incidence and witnesses, and replays every certificate.
`make projected-replay-data` and `make projected-replay` reproduce the
completed Lean proof and final axiom audit.

The original proof archive is `q5-certificates.tar.gz` (3,516,042 bytes), SHA-256:

```text
2792f86f9b87bc231aafe94679b9abd90b28163748ba7821e00371cd7699d1a3
```

It contains 357 `Q5P2` files. Each begins with a four-byte magic value and a
156-byte root-case header, followed by a prefix tree of closing claims,
refinements and splits. The header is compared with the corresponding line
of `q5-threshold-cases-size15.txt` before replay. See the separate checker in
`src/check_five_colour_certificate.cpp` for the compact executable format.

`five-colour-geometry.txt` contains the 75 canonical face tuples and the 75×75
target/source corner masks. `q5-cases-size15.txt` is the original anchored
cover; its repeated-variety cases are combined with the 113 cases in
`q5-distinct-shared-cases-size15.txt` to form the final 357-case cover. The
cases can overlap. The independent physical audit checks all orbit coverage
and all exported capacities.

`q5-three-variety-obstruction.json` records 4A+5B+5C. The other saved collections
supply positive controls and supplementary checks. The size-12 repeated-colour
and three-variety records are retained because the original geometric audit
checks them too; their additional results are not claimed as Lean theorems.
The exact-search and interval-search records support reproducibility of the
original computations. Current verification summaries are generated under
ignored `build/checks/`, not stored as supposedly current validation logs.

## Regenerate

The finite geometry and case generation use Python's standard library:

```sh
python3 -S scripts/five_colour_geometry.py
python3 -S scripts/five_colour_cases.py --output data/q5-cases-size15.txt
python3 -S scripts/five_colour_distinct_cases.py --output data/q5-distinct-shared-cases-size15.txt
python3 -S scripts/five_colour_threshold_cases.py --output data/q5-threshold-cases-size15.txt
```

`make check` checks the saved final inputs directly against physical geometry.

To rerun the interval search and reconstruct the archive:

```sh
make certificates
mkdir -p data/q5-certificates
build/five_colour_boxes data/five-colour-geometry.txt data/q5-threshold-cases-size15.txt data/q5-boxes-size15.json 120 8 data/q5-certificates/case-
python3 -S scripts/pack_five_colour_certificates.py
python3 -S scripts/check_five_colour_certificates.py
```

The search limit is per case. A timeout is not a proof; the packer requires
all cases to finish UNSAT. An alternative valid archive can have different
bytes, so changing the checked archive requires reviewing its hash in
`scripts/check_package.py` and this document. Raw certificates are an ignored
cache. The archived certificate hash matches the research checkout exactly.

The fixed `lean-small-replay-cases.json` selects all 105 certificates with at most
500 instructions directly from the original archive bytecode. It is checked by
`python3 -S scripts/small_replay_cases.py --check`; `make small-replay` verifies
the corresponding Lean proofs and their linked integer exclusions.

The rejection fixture `q5-distinct-known-control.txt` has total G=11, one fixed
opposite-repeat anchor, 0–1 coordinate bounds and budget zero. The physical audit
normalises the saved eleven-cube witness and checks these bounds, the budget and
failure of every target. It is a separate problem from the G=15 exclusion cases.
