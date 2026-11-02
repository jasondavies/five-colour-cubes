# Mathematical inputs and certificates

The durable proof archive is `q5-certificates.tar.gz` (3,516,042 bytes), SHA-256:

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
