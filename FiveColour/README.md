# Formalisation scope and reproduction

The physical sharp threshold 15 is fully formalised. All 279 projected
certificates, final theorem assembly and the axiom audit have passed.
`Packed.ProjectedChunks.threshold15` and `sharpThreshold15` are unconditional
proofs of `Physical.Threshold15` and `Physical.SharpThreshold15`.

The default build checks the geometry, reductions, checking infrastructure and
selected certificates. Reproduce the full proof with `make projected-replay-data`
and `make projected-replay`; the complete generated replay is an opt-in target.

| Component | Scope |
| --- | --- |
| `Puzzle.lean`, `ComparatorBridge.lean` | Geometric comparator definitions without a catalogue, equivalence to the enumerated-rotation model, and the unconditional fourteen-cube obstruction. Sharpness and least-size transfers retain the upper bound as a hypothesis. |
| `Problem.lean` | Physical cubes, distinct copies, solutions and intended threshold propositions. Proves corner–rotation equivalence using the pinned generic theorem and that the lower family uses all five colours. |
| `CatalogueData.lean`, `CatalogueChecks/`, `Catalogue.lean` | Kernel-checked coverage of all 15,625 face assignments, all-five-colour validity, and uniqueness of the 75 proper-rotation varieties. |
| `Geometry.lean` | Source rotation invariance and transport of solutions between rotated targets. |
| `CornerKeys.lean`, `CornerKeyData.lean` | Compact cyclic corner keys; equality is proved equivalent to cyclic equality of triples. |
| `PhysicalIncidence.lean` | Calibrates the keys against all 600 physical corners and proves all 45,000 compatibility bits correct. |
| `Matching.lean` | Physical copy assignments are equivalent to Hall's cardinality inequalities, using mathlib's finite Hall theorem. |
| `Multiplicity.lean` | Exact counting by variety, conservation of total mass, physical neighbourhood sums and the bound of seven copies per variety in a counterexample. |
| `HallCuts.lean` | All nonempty corner sets occur among the 255 masks; physical failure is equivalent to reference-checker admissibility. |
| `PackedHall*.lean` | Checks every packed neighbourhood mask and deficiency bound against the reference cuts, and transports physical counterexamples into valid packed vectors. |
| `Symmetry.lean`, `SymmetryAction.lean` | Global colour permutations and reflection preserve solvability and induce bijections of varieties with exact multiplicity transport. |
| `SymmetryConstraints.lean` | Transports corner sets, Hall neighbourhoods and anchor budgets under those symmetries. |
| `AnchorKinds.lean` | The adjacent/opposite distinction, counts 60 and 15, and transport of class-specific capacity bounds. |
| `NormalisationData.lean`, `AnchorNormalisation.lean` | Face-level colour-permutation witnesses for all 75 varieties, the exact two-orbit theorem, and normalised physical counterexamples with the generator's anchors 3 and 0. |
| `Anchor.lean` | The anchor Hall lemma, giving the budget `7 - m - |K|` for every chosen anchor. |
| `TwoVarieties.lean` | Hall-based construction from two varieties, and the resulting multiplicity cap in any physical counterexample. |
| `PairCapacityDefs.lean`, `PairCapacityData.lean`, `PairCapacities.lean` | Checks 1,200 witness-table entries against physical incidence and proves the capacity table sound. Zero entries use the general seven-copy bound. |
| `RootCapacity*.lean`, `RootCapacities.lean` | Checks all 26,775 exported upper bounds and proves root-box membership under the chosen anchor, class and Hall-budget premises. The anchor sentinel is interpreted as its fixed multiplicity. |
| `CoverMasks.lean` | Mask decoding agrees with physical anchor neighbourhoods; bitwise transport agrees with image of a set of varieties. Defines the eligible covers, retaining the distinct/all-adjacent exception explicitly. |
| `StabiliserData.lean` | Certifies 16 global symmetry actions on all 75 varieties by face-level proper-rotation witnesses. No completeness claim about the list of symmetries is needed. |
| `CoverData.lean`, `CoverChecks*.lean` | Verifies all 512 cover transports and all 1,537 eligible cover/multiplicity lookups against the exported root metadata and neighbourhood masks. |
| `CoverReduction.lean` | `Physical.reduce_anchor_cover` preserves physical failure and the root premises under a chosen symmetry, then places the transformed multiplicity vector in an exported root box. |
| `SharedCorners.lean` | Twenty repeated-colour corner types, two per adjacent variety, the eleven-variety pigeonhole theorem, and a positive non-anchor mass excluding cover 252 after normalisation. |
| `AnchorSelection.lean` | Chooses a used anchor satisfying the generator's class caps and supplies the shared-corner exclusion when all varieties are distinct and adjacent. |
| `CaseCoverage.lean` | `Physical.physical_root_cover` places every counterexample with at least eleven copies in a transformed exported root box, with all root premises proved. |
| `CaseProblem.lean` | Defines the 78 integer constraint families in archive order, proves their admissibility for a fifteen-cube counterexample, and derives the threshold conditionally on all integer root exclusions. |
| `ArchiveCore.lean`, `ArchiveData.lean`, `ArchiveChecks*.lean` | Verifies the encodings and semantic fields of all 357 actual Q5P2 headers against the integer root model. |
| `ArchiveBridge.lean` | Proves exact box and 78-family problem equivalence; supplies the threshold and sharp-threshold implications from all concrete archive exclusions. |
| `RootContainment.lean` | Cut and box monotonicity, transport of complete integer root problems, and direct exclusion by an impossible initial budget. |
| `RootReductionChecks.lean`, `RootReduction.lean` | Checks 49 root containments and 29 direct arithmetic exclusions, proves that every physical counterexample lies in one of 279 remaining roots, and supplies the reduced archive-to-threshold interface. Original case IDs and certificates are unchanged. |
| `ArchiveExamples.lean` | Connects three existing direct certificate proofs to the integer case-cover interface. |
| `Chunked/Link.lean`, generated `ReplayChunks/Link.lean` | Checks the concrete replay declarations against the verified archive model, preserving case numbers for selected or reordered lists. |
| `BudgetProjection.lean`, `RootProjection.lean`, `ProjectedChecks*.lean`, `ProjectedBridge.lean` | Proves deletion with fixed anchor, checks all 279 projected headers, and identifies their complete integer and packed models. |
| generated `ProjectedChunks/Threshold.lean` | Checked unconditional physical threshold and sharpness theorems, composing all 279 certificate proofs. Outside the default build; reproduced by full projected replay. |
| `LowerData.lean`, `LowerBound.lean` | Explicit deficient corner sets and the theorem `Physical.lower_bound`: the fourteen physical cubes use all five colours and admit no solution. |
| `BoxCertificates.lean` | Sound interval refinement and certificate checking for finite integer vectors. |
| `FastCertificates.lean` | Sound intersection/union summaries of feasible cuts. |
| `PackedArithmetic.lean` | Base-1024 subset sums, no-carry bounds, decoding and mask calibration. |
| `PackedSemantics.lean` | Connection between packed arithmetic and the integer box model. |
| `PackedVerified.lean` | Sound fast checking with guarded split values. |
| `PackedCalibration*.lean` | Kernel calibration of all 19,125 Hall-cut weights against their masks. |
| `PackedChunks.lean` | Composition of checked chunks with exact boundary comparisons and supplied exclusion proofs. |
| `PackedCase*.lean`, `Chunked/` | Selected actual certificates and their exclusion theorems. |

## Correspondence with the paper

The geometric challenge and the proof's physical model express the same puzzle:

| Paper condition | Lean statement |
| --- | --- |
| Each face has one of five fixed colours, and every colour occurs on each source and on the target. | `Cube := Fin 6 → Fin 5`; `UsesAllColours` is surjectivity. Source validity is a theorem hypothesis; target validity is part of `HasSolution`. |
| Collections may repeat varieties. | `Fin n → Cube` indexes physical copies; the family need not be injective. |
| Choose eight distinct copies. | The placement is an embedding `Fin 8 ↪ Fin n`. |
| Rotate each selected copy; reflections are not moves. | `Puzzle.HasSolution` uses determinant-positive signed coordinate permutations. `hasSolution_iff` identifies these with the proof's table of 24 proper rotations. |
| Exterior faces are monochromatic; internal faces are unrestricted. | At each of the eight positions only its three `exposedFaces` must match the single target face assignment. The compared `ColourCubes.exposed_face_rule` fixes their geometric meaning. |
| The target may depend on the collection. | `HasSolution` existentially quantifies the target inside the universal quantification over source families. |
| Fourteen can fail: four copies of A, five of B and five of C. | `lowerFamily` uses indices 0–3, 4–8 and 9–13, with the paper's three face tuples. `Puzzle.lower_bound` proves palette validity and failure. |
| Fifteen is the least guaranteed size. | `solution_of_threshold` selects fifteen from any larger collection; `least_of_threshold` combines that implication with the fourteen-cube obstruction. `Solution.lean` applies these transfers to the completed threshold theorem. |

The colour relabellings and global reflections in the case reduction transport
whole hypothetical counterexamples and preserve solvability. They add no moves
to `HasSolution`. All anchor-selection and cover premises are discharged in
`counterexample_integer_root`; only the concrete archive exclusions remain in
`Archive.threshold_of_exclusions`. The projected replay supplies these exclusions through the checked deletion
lemma and retained-root coverage.
Alternatively, `Physical.root_exclusions_of_reduced` recovers that same
357-root interface from the 279 members of `Physical.replayRoots`.
`Physical.counterexample_reduced_root` proves the corresponding physical
coverage theorem, and `Archive.sharp_threshold_of_reduced_exclusions` uses
only those archive exclusions. The membership and cardinality checks are
kernel proofs; the generator merely proposes the finite witnesses.

Regenerate or check the reduction with
`python3 -S scripts/generate_five_colour_reduction.py [--check]`.
Build its proofs with `lake build FiveColour.RootReduction`.

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
python3 -S scripts/generate_five_colour_hall.py
python3 -S scripts/generate_five_colour_symmetry.py
python3 -S scripts/generate_five_colour_capacities.py
python3 -S scripts/generate_five_colour_coverage.py
python3 -S scripts/generate_five_colour_archive.py
python3 -S scripts/generate_five_colour_reduction.py
python3 -S scripts/generate_five_colour_projection.py
python3 -S scripts/generate_five_colour_packed.py
python3 -S scripts/generate_five_colour_chunks.py
```

These serializers are untrusted. Lean checks numerical acceptance, calibration,
valid initial bounds and composition. There is no `native_decide`, proof hole
or added axiom in the proof sources. The audited dependencies are confined to
`propext`, `Classical.choice` and `Quot.sound`.

The preferred full replay uses `make projected-replay-data` followed by
`make projected-replay`; see the root README for concurrency and stop/resume
instructions. `Packed.Projected.sharp_threshold_of_exclusions` consumes exactly
the 279 projected exclusions, totalling 499,829 instructions. The generated
`ProjectedChunks.Threshold` module supplies them and proves the unconditional
physical threshold and sharpness; its four-declaration audit uses only standard axioms.

The three checked interfaces describe successive stages of the same reduction:

| Stage | Conditional theorem | Module |
| --- | --- | --- |
| Original 357 integer roots | `Physical.threshold_of_integer_root_exclusions` | `CaseProblem.lean` |
| 279 retained roots, with their original total and budget | `Physical.threshold_of_reduced_root_exclusions` | `RootReduction.lean` |
| 279 projected packed problems | `Packed.Projected.sharp_threshold_of_exclusions` | `ProjectedBridge.lean` |

`ArchiveBridge.lean` identifies the original packed archive with the integer
roots through `Packed.Archive.root_model` and `problem_model`.
`RootReduction.lean` also supplies
`Packed.Archive.sharp_threshold_of_reduced_exclusions`, reusing original
case IDs and certificates. The original 357-case route remains available with
`make replay-data` and `make replay`.

Original and projected integer problems specialise `Physical.caseProblem`,
whose `caseProblem_admissible_iff` characterises the prescribed total, anchor
budget and 75 target-failure families. `BudgetProjection.lean` proves trimming
while preserving the anchor; `RootProjection.lean` applies it after original
root selection. `ProjectedChecks*.lean` check all new headers and their
coverage. `ProjectedBridge.lean` identifies the complete projected box and
admissibility predicate, including totals from 9 to 15, with the packed archive.

`Physical.counterexample_packed_vector` proves that any physical counterexample
has an exact base-1024 encoding with digits at most seven, the correct total
mass, and one satisfied packed Hall deficiency for each target. It introduces
no case-cover assumption. `Physical.anchor_cover` separately proves the root
budget before symmetry reduction. `Physical.normalised_anchor_cover` transports
a chosen anchor to the generator's representative, and
`Physical.anchor_budget_transport` justifies transforming its cover constraints
by stabilisers. `Physical.exported_cover` verifies that every eligible cover's
neighbourhood and budget map to an actual ledger row. `Physical.reduce_anchor_cover`
then transports the counterexample and all root premises, using
`Physical.exported_root_contains` for box membership. Eligibility excludes cover
252 only when the anchor is adjacent and the maximum multiplicity is one.
`Physical.select_anchor` now supplies the anchor and class bounds; the shared
repeated-colour corner forces positive mass in the exceptional neighbourhood,
contradicting its zero budget. `Physical.physical_root_cover` consequently has
no anchor-selection or eligibility hypothesis. For fifteen copies,
`Physical.counterexample_integer_root` produces an integer vector satisfying
all 78 constraint families inside one of the exported root boxes. The capacity and coverage generators copy the actual ledger data,
with reproducibility checked by `--check`.

The lower-bound proof uses Hall's necessary inequality, proved directly from
the injectivity of the copy assignment. Of the 75 targets, 72 have an unavailable
corner; the other three have deficient sets of sizes 5, 6 and 6. This finite
check is a different route from the paper's elementary classification of the
three possible targets. Catalogue completeness and target-rotation transport
extend the obstruction to every physical target, in any orientation.

The package imports its physical model, corner matching and rotation transport
from the pinned `colour-cubes-core` library. `Puzzle.HasSolution` specialises the
shared geometric model to targets using all five colours; `Physical.HasSolution`
is its equivalent enumerated-rotation form.

The root `Challenge.lean` imports only Mathlib and has five intentional theorem
holes. It is excluded from the proof library. `Solution.lean` supplies those
statements from the completed projected replay and builds successfully in Lean.
The full external comparator check is running. `make check-comparator-lower` compares only the exposed-face
rule and explicit obstruction; `make comparator` checks the full interface.
