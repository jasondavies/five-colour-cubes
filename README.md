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
the anchor Hall budget. Full kernel replay and the symmetry and capacity
reduction to the 357 root cases remain outstanding. `Threshold15` and `SharpThreshold15`
are propositions in `FiveColour/Problem.lean`, not proved theorems. The generic
corner–rotation equivalence is already available from the pinned dependency.

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
cuts and Hall transpose, builds the default Lean target and audits twenty-five
theorems.
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
builds the aggregate theorem and audits its axioms.

To stop this package's runner, create
`build/five-colour-chunks/ReplayChunks/STOP`. Remove it before resuming.
Do not regenerate sources during replay. The research checkout's ongoing run
is separate; creating this package does not move, restart or duplicate it.

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
access, review the manuscript and then prepare the independent comparator
challenge and Palomar metadata. There is no completed comparator interface yet.
