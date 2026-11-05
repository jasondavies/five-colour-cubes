# Publication proof inputs

The complete Lean proof uses `q5-projected-certificates.tar.gz`: 279 certificates,
499,829 instructions, 1,134,573 uncompressed bytes and 313,094 compressed bytes.
Its SHA-256 is:

```text
e7b40f79831b5e0a44b374397d90bc4068f43d07e4226e1a45a829fd5b900e4a
```

`q5-projected-root-cases.txt` specifies the problems. The fixed
`q5-projected-root-manifest.json` maps local indices to original root IDs,
records every certificate hash and gives two zero-budget counterexamples
explaining the exceptional budget-one cases. These are proof inputs, not
mutable verification logs.

Each `Q5P2` certificate starts with a four-byte magic value and a 156-byte
problem header, followed by a prefix tree of closing claims, refinements and
splits. The independent C++ checker is `src/check_five_colour_certificate.cpp`.
Lean verifies the same rules and their soundness; the exporter is untrusted.

| Input | Role in the retained proof |
| --- | --- |
| `five-colour-geometry.txt` | 75 canonical face tuples and the 75×75 target/source corner masks. |
| `q5-cases-size15.txt` | Anchored Hall-cover cases, used to generate and independently check the repeated-variety cover. |
| `q5-distinct-shared-cases-size15.txt` | 113 distinct-variety cases, including the shared-corner reduction. |
| `q5-threshold-cases-size15.txt` | Combined 357-root cover. These definitions are still required even though the old certificate archive is not. |
| `q5-root-reduction.json` | Checked containments and arithmetic exclusions leaving 279 roots. |
| `q5-projected-root-*`, `q5-projected-certificates.tar.gz` | Current projected problems, mappings, witnesses and certificates. |
| `five-colour-extremal.json` | Face tuples, repeat colours and orbit sizes for all five three-variety obstruction classes. |
| `q5-three-variety-obstruction.json` | The fourteen-cube lower-bound witness and manuscript figure input. |
| `q5-local-distinct.json`, `q5-distinct-known-control.txt` | An independently checked failing eleven-cube pool and a root containing it; invalid closing claims must be rejected. |

## Verification and regeneration

Run `make verify-full WORKERS=2` for the complete proof. `make check-code` checks
physical geometry, root coverage, current certificates, 80 rejected negative
controls and generated Lean data. The physical quarter-turn reconstruction is
shared within the audit process, independently of the search model.

The negative controls include truncation, trailing bytes, a false mass claim,
and all 77 direct closing claims on the known failing eleven-cube pool. Lean's
`CertificateControls.lean` also checks exact checkpoint boundaries and rejects
out-of-range splits. The full Lean replay checks all 279 real proof objects.

To regenerate the geometry and case definitions:

```sh
python3 -S scripts/five_colour_geometry.py
python3 -S scripts/five_colour_cases.py --output data/q5-cases-size15.txt
python3 -S scripts/five_colour_distinct_cases.py --output data/q5-distinct-shared-cases-size15.txt
python3 -S scripts/five_colour_threshold_cases.py --output data/q5-threshold-cases-size15.txt
```

All current Lean-table serializers support `--check`, as listed in the Makefile.
`make replay-data` deterministically exports the saved certificates into retained
`FiveColour/ProjectedChunks/`; `make replay` checks their complete assembly.
Current reports belong under ignored `build/`, not in this input directory.

The old 357-certificate archive, partial replay inventory, exact-search program
and historical solver reports are retained in Git history through commit
`aeb81d0`. They are not needed to reproduce the current proof. The retained
`src/five_colour_boxes.cpp` can search for interval certificates for the current
root file, but rerunning search is not required for verification. A new valid
certificate archive may have different bytes and requires updating and checking
its manifest; a solver timeout is never an exclusion proof.
