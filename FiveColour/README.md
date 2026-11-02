# Formalisation scope and reproduction

This is a partial formalisation of the sharp threshold 15. A successful default
build establishes the physical catalogue, fourteen-cube obstruction, checker
theorems and selected exclusions below. It
does not establish the physical threshold.

| Component | Scope |
| --- | --- |
| `Problem.lean` | Physical cubes, distinct copies, solutions and intended threshold propositions. Proves corner–rotation equivalence using the pinned generic theorem and that the lower family uses all five colours. |
| `CatalogueData.lean`, `CatalogueChecks/`, `Catalogue.lean` | Kernel-checked coverage of all 15,625 face assignments, all-five-colour validity, and uniqueness of the 75 proper-rotation varieties. |
| `Geometry.lean` | Source rotation invariance and transport of solutions between rotated targets. |
| `CornerKeys.lean`, `CornerKeyData.lean` | Compact cyclic corner keys; equality is proved equivalent to cyclic equality of triples. |
| `PhysicalIncidence.lean` | Calibrates the keys against all 600 physical corners and proves all 45,000 compatibility bits correct. |
| `LowerData.lean`, `LowerBound.lean` | Explicit deficient corner sets and the theorem `Physical.lower_bound`: the fourteen physical cubes use all five colours and admit no solution. |
| `BoxCertificates.lean` | Sound interval refinement and certificate checking for finite integer vectors. |
| `FastCertificates.lean` | Sound intersection/union summaries of feasible cuts. |
| `PackedArithmetic.lean` | Base-1024 subset sums, no-carry bounds, decoding and mask calibration. |
| `PackedSemantics.lean` | Connection between packed arithmetic and the integer box model. |
| `PackedVerified.lean` | Sound fast checking with guarded split values. |
| `PackedCalibration*.lean` | Kernel calibration of all 19,125 Hall-cut weights against their masks. |
| `PackedChunks.lean` | Composition of checked chunks with exact boundary comparisons and supplied exclusion proofs. |
| `PackedCase*.lean`, `Chunked/` | Selected actual certificates and their exclusion theorems. |

Run from the repository root:

```sh
lake build FiveColour
python3 -S scripts/audit_lean.py
make examples
```

The default target contains cases 79, 165 and 207. `make examples` checks cases
78, 326 and 7 using bounded chunks, including the 9,811-instruction example.
The reference implementation and its original examples are retained for
comparison; they can be built individually as `FiveColour.Case79`, etc.

Regenerate the catalogue witnesses, lower-bound cuts, packed data and examples with:

```sh
python3 -S scripts/generate_five_colour_catalogue.py
python3 -S scripts/generate_five_colour_packed.py
python3 -S scripts/generate_five_colour_chunks.py
```

These serializers are untrusted. Lean checks numerical acceptance, calibration,
valid initial bounds and composition. There is no `native_decide`, proof hole
or added axiom in the proof sources. The audited dependencies are confined to
`propext`, `Classical.choice` and `Quot.sound`.

The full archive is generated and replayed with `make replay-data` and
`make replay`; see the root README for bounded concurrency and stop/resume
instructions. Completing that run still leaves the reduction of arbitrary
size-15 physical collections to the 357 roots: the matching/Hall equivalence,
transport to multiplicity vectors, and the symmetry and capacity arguments
behind case coverage. No theorem proves `Physical.Threshold15` or
`Physical.SharpThreshold15` yet.

The lower-bound proof uses Hall's necessary inequality, proved directly from
the injectivity of the copy assignment. Of the 75 targets, 72 have an unavailable
corner; the other three have deficient sets of sizes 5, 6 and 6. This finite
check is a different route from the paper's elementary classification of the
three possible targets. Catalogue completeness and target-rotation transport
extend the obstruction to every physical target, in any orientation.

The default package imports generic corner and rotated-slot lemmas from the
pinned four-to-three project; it does not use that project's threshold theorem.
