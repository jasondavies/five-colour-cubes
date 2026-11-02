# Formalisation scope and reproduction

This is a partial formalisation of the sharp threshold 15. A successful default
build establishes the checker theorems and the selected exclusions below. It
does not establish the physical threshold.

| Component | Scope |
| --- | --- |
| `Problem.lean` | Physical cubes, distinct copies, solutions and intended threshold propositions. Proves corner–rotation equivalence using the pinned generic theorem and that the lower family uses all five colours. |
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

Regenerate the packed data and examples with:

```sh
python3 -S scripts/generate_five_colour_packed.py
python3 -S scripts/generate_five_colour_chunks.py
```

These serializers are untrusted. Lean checks numerical acceptance, calibration,
valid initial bounds and composition. There is no `native_decide`, proof hole
or added axiom in the proof sources. The audited dependencies are confined to
`propext`, `Classical.choice` and `Quot.sound`.

The full archive is generated and replayed with `make replay-data` and
`make replay`; see the root README for bounded concurrency and stop/resume
instructions. Completing that run still leaves three physical obligations:
connect the concrete catalogue/incidence masks to proper rotations, cover
arbitrary size-15 collections by the 357 roots, and prove the size-14 physical
counterexample. No theorem proves `Physical.Threshold15` or
`Physical.SharpThreshold15` yet.

The default package imports the generic corner lemma from the pinned
four-to-three project; it does not use the four-to-three threshold theorem.
