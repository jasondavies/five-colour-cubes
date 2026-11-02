# The sharp corner threshold for five-colour cubes

- [Paper (PDF)](paper/macmahon-five-colour-threshold.pdf) and [LaTeX](paper/macmahon-five-colour-threshold.tex).
- [Physical target statements](FiveColour/Problem.lean), [fourteen-cube lower bound](FiveColour/LowerBound.lean), and [formalisation guide](FiveColour/README.md).
- [Interval checker](FiveColour/BoxCertificates.lean), [packed checker](FiveColour/PackedVerified.lean), and [chunk composition](FiveColour/PackedChunks.lean).
- [Provenance and verification scope](formalization.yaml).

**Every collection of fifteen cubes using all five fixed face colours contains
eight that build a five-colour target. Fourteen need not suffice.** The target
is a 2×2×2 cube with monochromatic exterior faces using all five colours.
Collections may repeat varieties; proper rotations are allowed and interior
faces are unrestricted.

The lower example is four copies of A, five of B and five of C, with faces
listed as `+x,-x,+y,-y,+z,-z`:

```text
A = (0,0,1,2,3,4)
B = (0,1,2,3,2,4)
C = (0,3,1,2,4,1)
```

The paper gives an elementary proof that this collection fails. Its upper
bound is computer-assisted: a complete reduction gives 357 root cases and a
separate C++ checker accepts every archived interval certificate. This supplies
the five-colour corner value listed as unknown in Table 7 of
[Berkove, Eickemeyer and Schulman (2018)](https://doi.org/10.5281/zenodo.10680216).

**The physical threshold is not yet proved in Lean.** Lean proves checker
soundness, packed arithmetic, chunk composition and selected case exclusions.
It also proves completeness and uniqueness of the 75 physical varieties,
correctness of every compatibility bit, and that the fourteen-cube example has
no solution. Physical Hall deficiencies are proved equivalent to the packed
checker's target constraints, with exact multiplicity counts, bounds 0–7 and
the anchor Hall budget. Colour permutations and global reflection preserve
solvability, multiplicities and Hall budgets; the two colour orbits and their
anchor representatives are certified. Lean also proves the two-variety capacity
bound and checks all 26,775 upper bounds in the 357 exported roots, conditional
on each root's anchor, class bounds and Hall budget. Verified physical symmetry
witnesses map every eligible anchor cover to an exported root, preserving those
premises. Anchor selection and the shared-corner exclusion are also proved:
every hypothetical fifteen-cube counterexample yields an admissible integer
vector in one of the 357 root boxes. All 357 packed archive headers and their
constraint families are proved equal to the integer models. The final assembly
is wired to consume the replay exclusions; complete archive replay and checking
that full assembly remain outstanding.
`Threshold15` and `SharpThreshold15` are propositions in `FiveColour/Problem.lean`,
not proved theorems. The generic corner–rotation equivalence is already available from the pinned dependency.

The research and manuscript were developed by GPT-6-Astra (OpenAI), used through
Codex, under Jason Davies's direction. Author review and submission approval of
the manuscript are pending. Automated checks are not independent human peer
review. The limited literature search does not establish priority; the October
2026 Rosenfeld article remains unread. This repository has not been published
or submitted to Palomar.

## Build and check

Requirements: Lean/mathlib v4.35.0, Python 3.12 or later, Make, and a C++20
compiler with OpenMP. The checks do not require OR-Tools, a SAT solver or a GPU.

```sh
lake exe cache get
make check WORKERS=2
make paper                 # additionally requires latexmk and LaTeX
```

`make check` checks dependency pins and source hygiene, verifies physical
geometry and case coverage, replays all 357 C++ certificates, rejects 80
negative controls, checks regeneration of the catalogue witnesses and lower-bound
cuts, Hall transpose, anchor-normalisation, capacity, cover and archive-header
witnesses, builds the default Lean target and audits fifty-nine theorems.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted. Default Lean
checks include all 19,125 packed-cut weight and semantic calibrations, plus three small real
certificates. They do not claim full archive replay.

The [larger examples](FiveColour/Chunked/) compose 499, 3,763 and 9,811 original
instructions into 5, 36 and 89 bounded chunks. Run `make examples` to build and
audit their aggregate theorem and check corrupted-checkpoint controls.

## Pinned geometry dependency

The package pins `macmahon-four-to-three` to
`6f5f04b28ac8d2156af66bbe060f2060b19b30a4`. It imports only
`ThreeColour.CornerGeometry` and `ThreeColour.FamilyGeometry`, which import
the proper rotations from `macmahon-min-universal-sets` at its pinned revision. It does not import either
project's classification theorem.

Anonymous GitHub access to the four-to-three dependency could not be verified
when this package was assembled: Git requested credentials. A build from a
fresh clone therefore requires access to that dependency. Before public
release, make the pinned revision accessible or supply appropriate CI access.
With the existing sibling checkout and its cached dependencies, use:

```sh
python3 -S scripts/bootstrap_local.py
make check WORKERS=2
```

The bootstrap checks dependency revisions, checks out the four-to-three
package at its pinned commit, and reuses matching local dependency caches.
These local paths are build conveniences under ignored `.lake/`; the manifest
contains portable Git URLs and fixed revisions.

## Complete Lean replay

```sh
make replay-data WORKERS=8
make replay WORKERS=8
```

Generation produces 109,449 chunks covering all 11,599,651 archive instructions
at the default limit of 128 instructions per chunk. Generated sources under
`FiveColour/ReplayChunks/` and logs under `build/` are ignored. The runner limits
concurrent case builds and resumes through Lake's dependency cache. Progress
is in `build/five-colour-chunks/ReplayChunks/progress.json`, updated when a case
finishes; individual large cases can take hours. On completion, the runner
checks every replay root and constraint family against the verified archive
headers, builds `FiveColour.ReplayChunks.Threshold`, and audits the physical
threshold and sharp-threshold theorems. Success is reported only after those
final checks pass.

To stop this package's runner, create
`build/five-colour-chunks/ReplayChunks/STOP`. Remove it before resuming.
Do not regenerate case sources during replay. After an older run, aggregate
links can be updated without regenerating the certificate bodies:

```sh
python3 -S scripts/generate_five_colour_chunks.py --all --links-only
make replay WORKERS=2
```

Lake reuses valid cached case proofs. The research checkout's ongoing run is
separate and retains its original runner; this package's updated final assembly
has not yet been checked against the complete archive.

## Replay performance experiments

```sh
python3 -S scripts/benchmark_five_colour_replay.py --case 78 --limits 128 256 512 --repeats 3
```

This generates fresh proofs of the same certificate at different chunk limits,
checks each exclusion theorem and its axioms, and records wall time, CPU time,
peak memory and Lean profiler output under ignored `build/replay-benchmark/`.
Runs are sequential with one Lean thread and asynchronous elaboration disabled
so profiler timings do not overlap. Variant order alternates between repeats.
The benchmark does not modify production replay sources or use cached case proofs.
Results include import/setup costs and reflect background machine load; a small
case does not predict the performance of the largest cases. The production
chunk limit remains 128.

## Comparator challenge

[Challenge.lean](Challenge.lean) imports only Mathlib. It defines the puzzle
using face colourings, signed coordinate permutations of determinant +1,
and eight distinct source indices. It assumes no cube catalogue, compatibility
matrix or certificate data. The five targets are the exposed-face rule, the
explicit fourteen-cube obstruction, the fifteen-cube upper bound, sharpness,
and the least guaranteed size.

[ComparatorBridge.lean](FiveColour/ComparatorBridge.lean) proves equivalence
with the physical model and the geometric lower bound. Its upper-bound
transfers explicitly assume `Physical.Threshold15`. These proofs are included
in the default build and axiom audit. `Challenge.lean` has five intentional
statement holes; neither the proof library nor `Solution.lean` imports it.

```sh
python3 -S scripts/bootstrap_local.py --materialize # if using sibling caches
make check-comparator-lower # only the face rule and fourteen-cube obstruction
# After complete archive replay and final theorem assembly:
make comparator            # all five targets
```

The local runner uses the toolchain's Lean kernel, NanoDa and con-ron, with
`CON_RON_JOBS=2` by default. The sandbox hides sibling repositories, so the
local bootstrap's `--materialize` option copies cached dependencies inside this
checkout without changing their sources or the portable manifest. The two-target lower-bound check has passed Lean, NanoDa and con-ron;
it does not certify the upper bound.
[Solution.lean](Solution.lean) connects the geometric statements to the generated
full-replay theorem, and is excluded from default build targets until that
replay is complete. The full comparator has not passed; no Palomar submission
has been made.

## Files and release status

- `FiveColour/`: proof infrastructure, physical definitions and selected replays.
- `src/`: C++ searches, separate certificate checker and untrusted chunk exporter.
- `scripts/`: generators, physical audits, package checks and replay driver.
- `data/`: compressed certificates, root cases, geometry and checkable witnesses.
- `paper/`: manuscript source and PDF.

See [data provenance and regeneration](data/README.md). No transient verification
logs are committed. The GitHub remote is the intended location
`https://github.com/jasondavies/macmahon-five-colour-threshold`.
Before submission, complete the physical Lean theorem, settle dependency
access, review the manuscript, run the full comparator and finalise Palomar
metadata. The comparator statement and bridge are prepared; verification of
the complete solution remains pending.
