# Formalisation scope and reproduction

The physical sharp threshold 15 is fully formalised. All 279 projected
certificates, final theorem assembly and the axiom audit have passed.
`Packed.ProjectedChunks.threshold15` and `sharpThreshold15` are unconditional
proofs of `Physical.Threshold15` and `Physical.SharpThreshold15`.

The default Lake target (`lake build`) checks the geometry, reductions, checking infrastructure and
checkpoint rejection controls. Reproduce the complete proof, including the
unconditional cuboid results, with `make verify-full`.

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
| `ArchiveBridge.lean` | Supplies the root-bound and cut-model equivalences shared by the projected threshold proof and fourteen-cube enumeration. |
| `RootContainment.lean` | Cut and box monotonicity, transport of complete integer root problems, and direct exclusion by an impossible initial budget. |
| `RootReductionChecks.lean`, `RootReduction.lean` | Checks 49 root containments and 29 direct arithmetic exclusions, proves that every physical counterexample lies in one of 279 remaining roots, and derives the threshold from the retained integer exclusions. Original case IDs are preserved. |
| `BudgetProjection.lean`, `RootProjection.lean`, `ProjectedChecks*.lean`, `ProjectedBridge.lean` | Proves deletion with fixed anchor, checks all 279 projected headers, and identifies their complete integer and packed models. |
| retained generated `ProjectedChunks/Threshold.lean` | Checked unconditional physical threshold and sharpness theorems, composing all 279 certificate proofs. Outside the default build; reproduced by full projected replay. |
| `LowerData.lean`, `LowerBound.lean` | Explicit deficient corner sets and the theorem `Physical.lower_bound`: the fourteen physical cubes use all five colours and admit no solution. |
| `BoxCertificates.lean` | Sound interval refinement and certificate checking for finite integer vectors. |
| `FastCertificates.lean` | Sound intersection/union summaries of feasible cuts. |
| `PackedArithmetic.lean` | Base-1024 subset sums, no-carry bounds, decoding and mask calibration. |
| `PackedSemantics.lean` | Connection between packed arithmetic and the integer box model. |
| `PackedComputations.lean` | Proved bit-mask validity test and scalar mask-weight conversion. |
| `PackedVerified.lean` | Sound fast checking with guarded split values. |
| `PackedCalibration*.lean` | Kernel calibration of all 19,125 Hall-cut weights against their masks. |
| `CertificateControls.lean` | Kernel-checked positive and negative controls for checkpoint reuse and split bounds. |
| `PackedPruning.lean` | Root-specific cut coverage, fixed-coordinate reduction and sound transfer to the original families. |
| `PackedChunks.lean` | Composition of checked chunks with exact boundary comparisons and supplied exclusion proofs. |

The extremal results are independent of the interval replay:

- `ExtremalMultiplicity.lean`: the maximum multiplicity in a fourteen-cube
  obstruction is at most five. `ExtremalMatching.lean` lifts explicit group allocations
  to distinct physical copies; `ExtremalSixChecks*.lean` checks the small local
  inventories after the anchor reduction and disjoint-source lemma (2,702
  six-copy cases and 35 four-disjoint cases). Their geometry shares 300
  disjoint-group masks and 24 optional singleton references.
- `ExtremalClassification.lean`: exactly five symmetry classes with three
  varieties. Own-source targets handle 5,143 normalized candidates, and a
  disjoint pair handles 199. `ExtremalTripleChecks*.lean` proves completeness
  of the 60-record remainder over both anchor kinds: four positive targets
  and 56 orbit witnesses. `ExtremalSymmetry.lean` proves
  completeness of the stabilizer used to establish inequivalence; reflections
  act on entire collections. `ExtremalExamples.lean` proves failure and support
  size for each representative.
- `ExtremalFamilyTheorems.lean`: the exact generalized-family criterion. Four
  uniform support patterns (300 Hall masks) prove failure precisely when the
  groups have disjoint repeat supports; two allocations prove the converse.
- `Inventory.lean`: shared multiplicity and inventory transport under physical
  symmetries, independent of the classification tables.

These use kernel-checked finite geometry and allocations alongside the paper's
elementary arguments; they do not claim a purely symbolic formalization of the
directed-cut normalization. The generators are untrusted, and every witness is
checked against the physical incidence theorem.

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
`counterexample_integer_root`. `Physical.root_exclusions_of_reduced`
recovers the original 357-root interface from the 279 members of
`Physical.replayRoots`. The projected packed exclusions transfer to these
retained integer roots through checked deletion and coverage;
`Physical.threshold_of_reduced_root_exclusions` then gives the physical result.
The membership and cardinality checks are
kernel proofs; the generator merely proposes the finite witnesses.

Regenerate or check the reduction with
`python3 -S scripts/generate_five_colour_reduction.py [--check]`.
Build its proofs with `lake build FiveColour.RootReduction`.

Run from the repository root:

```sh
lake build FiveColour
python3 -S scripts/audit_lean.py
```

Regenerate the catalogue witnesses, lower-bound cuts, packed data and incidence with:

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
python3 -S scripts/generate_five_colour_incidence.py
make replay-data
```

These serializers are untrusted. Lean checks numerical acceptance, calibration,
valid initial bounds and composition. There is no `native_decide`, proof hole
or added axiom in the proof sources. The audited dependencies are confined to
`propext`, `Classical.choice` and `Quot.sound`.

Use `make verify-full` to check the retained replay sources without rewriting
them and then verify the complete proof. `make check-replay-data` checks their
regeneration separately; `make replay-data` explicitly replaces them. See the
root README for concurrency and stop/resume instructions. `Packed.Projected.sharp_threshold_of_exclusions` consumes exactly
the 279 projected exclusions, totalling 298,167 instructions. The generated
`ProjectedChunks.Threshold` module supplies them and proves the unconditional
physical threshold and sharpness; its axiom audit uses only standard axioms.

The three checked interfaces describe successive stages of the same reduction:

| Stage | Conditional theorem | Module |
| --- | --- | --- |
| Original 357 integer roots | `Physical.threshold_of_integer_root_exclusions` | `CaseProblem.lean` |
| 279 retained roots, with their original total and budget | `Physical.threshold_of_reduced_root_exclusions` | `RootReduction.lean` |
| 279 projected packed problems | `Packed.Projected.sharp_threshold_of_exclusions` | `ProjectedBridge.lean` |

`ArchiveBridge.lean` identifies the original packed bounds with integer roots
through `Packed.Archive.root_model`, and supplies the shared cut-model lemmas.
The original 357 root definitions remain part of the coverage proof.

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

The root `Challenge.lean` imports only Mathlib and has fifteen intentional
theorem holes. It is excluded from the proof library. `Solution.lean` supplies
the corner, cuboid, support, extremal and universal-collection statements. `SubmissionModel.lean`
restates the physical models without a catalogue; `SubmissionBridge.lean` proves
that rotation classes, physical copy counts, global symmetries and box slots
agree with the models used by the proofs. External comparison uses Lean and NanoDa.
`make check-comparator-lower` compares only the exposed-face rule and explicit
obstruction; `make comparator` checks the full interface.

## Larger cubes and small supports

`FiniteHall.lean` proves two general matching lemmas: sufficiently many copies
that fit every position, and a partial matching on exceptional positions with
large neighbourhoods elsewhere. `RareGeometry.lean` verifies the frame
compatibility bounds and the unique opposite-repeat variety determined by two
missing bichromatic pairs. Its compact edge bits are checked against physical
face adjacency; corner counts reuse the already verified incidence table.

The sharp frame argument is organised as follows:

- `RingData.lean` records the nine varieties lacking each bichromatic pair,
  their corner permutations and the common compatibility pattern.
  `RingGeometry.lean` checks every entry against the physical catalogue.
- `WeightedHall.lean` turns finite lists of Hall inequalities into matchings.
  `RingWeights.lean` verifies the ten inequalities needed per ring target and
  proves the target-selection arithmetic for arbitrary multiplicities.
- `ExtraHall.lean` handles an extra cube at a prescribed position.
  `RingEleven.lean` proves all three eleven-copy lemmas; `FixedPair.lean`
  translates them to physical cubes and distinct-copy placements.
- `FixedPairReserve.lean` supplies the reserves and selections needed by the
  general frame proof. `SharpGeometry.lean` checks the shared-corner and
  missing-pair facts. `DeficitHall.lean` isolates the final two-rare-pair case.
- `BoxThresholds.lean` proves the general cuboid classification. The
  `CubeBoxBridge.lean` equivalences identify cube and equal-side cuboid
  positions, preserving exposed faces, compatibility and physical placements.
  `SharpFrames.lean` and `FrameResults.lean` specialise the cuboid results to
  the cube formulas, including the corner exception; there is no separate
  sharp cube-frame case analysis.

`Reserve.lean` supplies disjoint monochromatic reserves for the preliminary
corner solution. The final Hall matching may rearrange these placements.
`FrameCompletion.lean` supplies the generic embedding extension and single-face
placement lemmas, adapted from the companion four-to-three development.
`BoxModel.lean` constructs complete boxes from frames; `FullCube.lean`
transports that construction through the equal-length equivalence.
`CubeModel.lean` retains the existing cube position definitions and cardinality
lemmas. The complete-cube threshold remains max(n³,15) for every n≥2.
`FramePools.lean` contains shared colour-pair helpers. `RareFrames.lean`
supplies the missing-pair definitions and reserve lemmas used by the frame proof.

`src/five_colour_fixed_pair.cpp` is a supplementary direct-rotation audit of
the geometry and all 75,582 eleven-copy collections in one missing-pair family.
It also checks all 1,800 extra-cube extensions of the 24 failing core collections.
The Lean argument uses multiplicity inequalities rather than that enumeration.

`SmallSupport.lean` proves thirteen cubes suffice with at most two varieties,
checks the twelve-cube counterexample, and derives the exact support thresholds
8, 13, 15. Its witness generator is `scripts/generate_five_colour_support.py`;
all witnesses are checked by the Lean kernel. `ExtremalFamilyTheorems.lean`
proves the general fourteen-cube obstruction family, including the
21-member subfamily, using uniform deficient corner sets.
The C++ program `src/five_colour_extensions.cpp`
regenerates geometry separately and checks the five pair-orbit witnesses.

The unconditional frame and complete-cube conclusions, and the combined
support threshold, are in `Solution.lean`. After projected replay, run
`make check-extensions` to build and audit them. `Audit.lean` includes the
conditional deductions and unconditional small-support lemmas;
`ExtensionsAudit.lean` audits the final wrappers. The geometric challenge includes the support and cuboid conclusions.

## Universal collections

`Universal.lean` proves that a fixed universal pool needs at least fifteen
sources, even when only adjacent-repeat targets are prescribed. For each
repeated colour, universality forces three physical sources: two sources,
each carrying at most two of the four bicoloured types, cannot match every
pair. The cardinalities of the five disjoint source groups then sum to at
least fifteen. `UniversalGeometry.lean` checks the small geometric facts and
the four-type combinatorial lemma in the kernel.

`UniversalStructure.lean` strengthens the necessity statement for a pool of
size fifteen: its varieties are all distinct and adjacent-repeat, with exactly
three sources per repeated colour. Their three smaller pairs form a spanning
tree on the other four colours. The proof combines the physical supplier lemma
with a kernel-checked three-pair lemma and Mathlib's tree criterion. These
structural conclusions are included in `Audit.lean`, but are outside the
current fifteen-claim comparator interface.

The fifteen-source upper witness is the cyclic orbit of three face tuples in
`Submission.universalFamily`. `UniversalData.lean` stores 75 injective copy
assignments, checked against the physical incidence theorem and transported
to arbitrary target orientations. The paper supplies a separate structural
Hall argument for this construction. Neither bound imports the threshold
certificates. `SubmissionBridge.lean` exports `universal_minimum` and
`universal_collection`; the latter includes validity, adjacent repeats,
distinct varieties and universality. Both have independent geometric
statements in `Challenge.lean` and appear in the extension axiom audit.
`make check-comparator-universal` checks these two claims with both external
kernels; it does not require the interval replay. Both claims also passed the
[complete fifteen-claim comparison](../verification/optimized-comparator.json).

## Cuboid classification

`BoxThresholds.lean` proves the complete classification for a, b, c ≥ 2:

- `box_frame_threshold_iff`: `BoxFrameThreshold a b c n` holds exactly when
  `max 15 (max (4*(a+b+c)-16) (2*(a+b+c)+1)) ≤ n`.
- `box_threshold_iff`: `BoxThreshold a b c n` holds exactly when
  `max (a*b*c) (max 15 (2*(a+b+c)+1)) ≤ n`.

These deductions take `Physical.Threshold15` as input. The unconditional
wrappers `FiveColour.Puzzle.box_frame_threshold` and `complete_box_threshold`
in `Solution.lean` apply the fully replayed corner theorem. Run
`make check-extensions` after reproducing that replay; no new interval
certificates or generated replay modules are needed for the cuboid results.

The proof is organised as follows:

- `BoxModel`, `BoxCounts`, `BoxAxes` and `BoxTransport` define corner, edge,
  face-interior and interior slots, prove their counts and physical rotation
  semantics, and handle permutations of side lengths and frame completion.
- `HallCover`, `MatchingCompletion`, `HalfMasks`, `ProjectionGeometry`,
  `ProjectionPool`, `ProjectionExtension`, `RingEight` and `EightPlusThree`
  prove that eight sources in a fixed missing-pair family plus any three
  sources have a corner target in that family. A failed Hall set supplies
  the small cover directly; no separate use of Kőnig's theorem is needed.
- `EightPairReserve` reserves monochromatic-edge sources in the whole
  collection, then retains enough of the prescribed missing-pair family.
  `BoxDirectional`, `BoxGeometry`, `RectCore`, `RectSmallHall` and
  `FamilyAlignment` give the weighted bounds used by `WideFrames`.
- `TargetChoice` shares the rare-pair target selection and supplier counts.
  `ThinChoice`, `ThinGeometry` and `ThinFrames` handle 2×2×3 and 2×3×3;
  `RodChoice` preserves the extra axial orientation for rods.
  `RodProfiles`, `RodBounds` and `RodFrames` handle 2×2×c; `StripProfiles`,
  `StripBounds` and `StripFrames` handle 2×3×c. `ConcentrationHall` turns a
  deficient Hall set into enough identical opposite-repeat sources to
  switch targets. The profile checks cover affine bounds and equality cases,
  so the resulting theorems apply to unbounded side lengths.
- `BoxLowerGeometry` and `BoxLowerBound` prove the uniform obstruction
  U + (S+5)V + (S+6)W for S=a+b+c−6. Combined with the corner obstruction
  and frame cardinality, it gives all three lower bounds.

`src/five_colour_box_geometry.cpp` separately reconstructs rotations and
checks the geometric claims. `scripts/generate_five_colour_corner_projections.py --check` verifies the generated signed projection tables. These checks
supplement the kernel proofs; no enumeration of source collections is used
in the cuboid deductions. `Audit.lean` lists the main conditional results
and physical bridges; `ExtensionsAudit.lean` includes the unconditional
classification and the three small thin-box examples.

## Replay operation and provenance

Run these commands from the repository root.

For cases with at least 3,500 instructions, generated replay sources use
root-specific cut lists: impossible alternatives are removed, fixed coordinates
are subtracted, equal residual neighbourhoods are merged, and alternatives
implying a weaker retained alternative are discarded. Lean checks the
replacement weights and a coverage witness for every original alternative.
The resulting exclusion is transferred back to the original root problem.
Smaller cases retain the full lists because validating the reduction has an
upfront cost. The packed base remains 1024.

`PackedFast.lean` evaluates digit places as powers instead of array lookups.
It proves equality with the original evaluator for every certificate, then
transfers the existing soundness theorem. The original checker remains the
reference semantics and continues to serve the enumeration proof.

`PackedComputations.lean` proves that containment in the packed all-seven
digit mask certifies bounded digits and exact reconstruction. Each checkpoint
uses two bit-mask equalities to establish the existing box-validity proposition.
The same module proves a scalar conversion from a 75-bit neighbourhood mask
to its reversed base-1024 weight; original and reduced calibration proofs
use this conversion without changing their statements.

The replay driver tries Lake's `--no-build` validation of the complete theorem
first. If anything is stale or missing, it falls back to bounded parallel case
builds. Artifact existence alone never counts as verification. The record says
whether the aggregate was already cached.

Defaults are two certificate workers and one Lean thread per process. On a
machine with more memory, raise `WORKERS`; do not assume more workers are faster.
`LEAN_NUM_THREADS` separately controls shared-library and extension builds.
The replay driver always gives each case one Lean thread. Memory use
increases with concurrent workers. Larger chunks can save a little time
while increasing peak memory, so the production limit remains 128.

### Developer tools

For measurements on the retained archive, without reusing a cached case proof:

```sh
python3 -S scripts/benchmark_five_colour_replay.py --case 120 --limits 128 256 512 --repeats 3
```

To compare the original and reduced lists on the same certificate:

```sh
python3 -S scripts/benchmark_five_colour_replay.py --case 19 --limits 128 --cut-modes original reduced --repeats 3
```

Case benchmark results include wall/CPU time and peak memory under
`build/replay-benchmark/`. Those experiments reuse the shared checker dependencies.

An optional minimization pilot first tries the existing direct closing rules,
then removes refinements and splits when an existing subtree also excludes
its larger parent box. Repeated passes can expose further reductions. It uses the C++ checker
as a search oracle and writes candidate copies under ignored
`build/certificate-minimization/`; it never rewrites the retained archive or
production Lean sources:

```sh
python3 -S scripts/benchmark_five_colour_minimization.py --cases all --passes 4 --label corpus
python3 -S scripts/benchmark_five_colour_minimization.py --cases 62 63 --measure both --cut-mode reduced --label timing
```

The first command checks candidates only in C++. The second proves the selected
complete certificate exclusions with the unchanged Lean checker, audits their
axioms, and separately times standalone replay of chunk acceptances and the
complete exclusion endpoint. The endpoint includes calibration, coverage,
checkpoint validity and soundness; the acceptance export isolates certificate
execution. Neither is the full Comparator. `--measure export` or
`--measure endpoint` selects only one scope. Measurements include the candidate hashes and input
identities. Promoting candidates still requires complete verification and a new
full Comparator run. Repeats alternate baseline and candidate order.

Do not delete `.lake` to tidy a publication package: it is already ignored,
and deleting it removes useful dependency/build caches.

Replay progress is in `build/five-colour-chunks/ProjectedChunks/progress.json`.
Create `build/five-colour-chunks/ProjectedChunks/STOP` to stop the case workers;
remove it and rerun the same command to resume. Completed modules stay cached;
interrupted cases restart. Do not regenerate sources during replay.

The [full verification workflow](../.github/workflows/full-replay.yml) uploads
verification records, stage and case logs, independent
audit reports and GNU time measurements as a `verification-<commit>-<attempt>`
artifact, including evidence from failed runs. Artifacts are retained for 90 days;
download the successful record for the permanent submission archive. GNU time's
maximum RSS is the largest process peak, not total concurrent build memory.
