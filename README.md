# Sharp thresholds for five-colour cube assemblies

- [Paper (PDF)](paper/five-colour-cubes.pdf) and [LaTeX](paper/five-colour-cubes.tex).
- [Cuboid results](#cuboid-thresholds), [extremal corner results](#extremal-corner-obstructions) and [universal collections](#universal-collections).
- [Reproduction](#verification) and [formalisation guide](FiveColour/README.md).
- [Provenance and verification scope](formalization.yaml).

**Every collection of fifteen cubes, each using all five colours of a fixed
palette, contains eight that build a five-colour target. Fourteen need not suffice.** The target
is a 2×2×2 cube with monochromatic exterior faces using all five colours.
A variety is a face colouring up to proper rotation. Collections may repeat
varieties; proper rotations are allowed and interior faces are unrestricted.

## Cuboid thresholds

A frame consists of the eight corners and noncorner edge positions of a box.
The thresholds F₅ and G₅ count available source cubes guaranteeing a frame or
a complete box, respectively; an assembly may use fewer cubes than are available.

**For all side lengths a, b, c ≥ 2, the exact thresholds are:**

- **F₅(a,b,c) = max(15, 4(a+b+c) − 16, 2(a+b+c) + 1)** for frames.
- **G₅(a,b,c) = max(abc, 15, 2(a+b+c) + 1)** for complete boxes.

The frame threshold depends only on the sum of the side lengths. It is 15
for sums 6 and 7, 17 for sum 8, and the frame's own position count for sums
at least 9. In particular, both sixteen-position frames, 2×2×4 and 2×3×3,
need one spare source. A single three-variety obstruction proves this extra
lower bound for both shapes.

For every shape except 2×2×2, 2×2×3 and 2×2×4, every collection of exactly
abc sources can be assembled into the complete box. Those three exceptions
have thresholds 15, 15 and 17. Thus **any twenty cubes form the frame of a
3×3×3 cube, and any 27 cubes form a complete 3×3×3 cube**.

| Box | Frame positions | F₅ | Volume | G₅ |
|---|---:|---:|---:|---:|
| 2×2×2 | 8 | **15** | 8 | **15** |
| 2×2×3 | 12 | **15** | 12 | **15** |
| 2×2×4 | 16 | **17** | 16 | **17** |
| 2×3×3 | 16 | **17** | 18 | 18 |
| 2×2×5 | 20 | 20 | 20 | 20 |
| 2×3×4 | 20 | 20 | 24 | 24 |
| 3×3×3 | 20 | 20 | 27 | 27 |

Bold entries need spare sources. From side sum 9 on, both thresholds equal
the number of positions.

The extra term 2(a+b+c) + 1 comes from one collection for every shape:
one U, τ+5 copies of V and τ+6 copies of W, where τ = a+b+c − 6. In face
order `+x,-x,+y,-y,+z,-z`, these varieties are:

```text
U = (0,1,0,2,3,4)
V = (0,1,1,2,3,4)
W = (0,3,1,4,2,3)
```

Only U, V and W can be targets. Each has too many positions restricted to a
particular source pool: U alone for target U, U together with V for target V,
and W alone for target W.

![Why U + (τ+5)V + (τ+6)W fails: each possible target has more corner and edge positions that only its pool fits than the pool has cubes](paper/uniform-obstruction.svg)

These results are proved in the paper and Lean. The extensions use Hall's
theorem, reservations and concentration of repeated varieties; no new
interval certificates are needed. The [aggregate classification](FiveColour/BoxThresholds.lean)
proves necessary and sufficient pool sizes in the physical model, including
all orientations and arbitrary repetitions. [Solution.lean](Solution.lean)
exports the unconditional `FiveColour.Puzzle.box_frame_threshold` and
`complete_box_threshold` by applying the completed corner theorem.

The paper also gives a constructive algorithm: at most 450 fixed-size flow
problems find a frame, with 225 configurations when two side lengths agree
and 75 for a cube. Decision and explicit construction take O(q) time for any
list of q sources in the word-RAM model. This complexity result is a manuscript proof,
not part of the Lean formalisation.

## Extremal corner obstructions

With at most k source varieties, the exact corner threshold is **8 for k=1,
13 for k=2, and 15 for k≥3**. Three varieties are therefore necessary for a
fourteen-cube obstruction. Every such obstruction has **maximum multiplicity
at most five**. Those using exactly three varieties have multiplicities
**(4,5,5)** and fall into **exactly five classes**, under common colour
relabelling and simultaneous reflection of the entire collection. Reflections
remain forbidden as individual cube moves.

The [multiplicity theorem](FiveColour/ExtremalMultiplicity.lean) and
[three-variety classification](FiveColour/ExtremalClassification.lean) are formalised
independently of the fifteen-cube certificate replay. The classification includes
exhaustiveness, failure of each representative, and pairwise inequivalence.
The [face-tuple dictionary](data/five-colour-extremal.json) lists representatives
and labelled orbit sizes. A [generalized obstruction family](FiveColour/ExtremalFamilyTheorems.lean)
keeps the four-copy variety fixed and allows mixtures within each five-cube
group. Such a collection fails exactly when no colour is the repeated colour
of a variety in both groups; examples can have maximum multiplicity four.
An independent audit checks all 202,575 labelled (4,5,5) collections, their 840 failures, the five orbits, and all 441 normalized family
distributions (91 failures and 350 solutions); its record is `build/checks/extremal.json`.

The lower example is four copies of A, five of B and five of C, with faces
listed as `+x,-x,+y,-y,+z,-z`:

```text
A = (0,0,1,2,3,4)
B = (0,1,2,3,2,4)
C = (0,3,1,2,4,1)
```

![Why 4A + 5B + 5C fails: each possible target has more corners that only its own variety fits than there are copies of that variety](paper/obstruction-figure.svg)

The paper's elementary proof first shows that only A, B and C themselves can
be targets. Each such target has more corners that only its own variety fits
than there are copies of that variety: five corners need A, with four copies,
and six need B or C, with five copies each.

The **56-class classification of all fourteen-cube obstructions is staged
separately**. The original 349-root route passed a complete Lean replay and
physical-endpoint axiom audit; its [provenance extract](verification/classification-baseline.json)
identifies the checked sources. The revised route excludes all 342 empty roots through one projection bridge:
137 use smaller Hall-budget projections, and 205 retain their original total
and budget. Only the seven nonempty roots use terminal enumeration. The
nontrivial projections reduce certificate instructions from
5,150,973 to 1,356,051. The revised route passed the complete Lean replay and physical-endpoint
axiom audit on 8 November; its [verification extract](verification/classification.json)
identifies those proof sources. The
[draft section](paper/classification.tex) is not yet included in the manuscript PDF.
The [classification route](data/classification-certificates.txt)
is separate from `verify-full` and from the current fifteen-claim Comparator
interface; neither certifies this additional result.

## Universal collections

A smallest fixed collection capable of building **every prescribed target**
has **15 cubes**, even if only the sixty adjacent-repeat targets are required.
This differs from the threshold theorem, which lets the target depend on an
arbitrary source collection. Every minimum universal collection has distinct
adjacent-repeat varieties; for each repeated colour, its three smaller pairs
form a spanning tree on the other four colours. This necessity statement is
proved in [UniversalStructure.lean](FiveColour/UniversalStructure.lean), separately
from the current comparator interface. One universal collection consists of all five
cyclic colour shifts of these three seeds (add 0 through 4 modulo 5 to every
colour), in face order `+x,-x,+y,-y,+z,-z`:

```text
(0,2,0,3,1,4)   (0,2,0,4,3,1)   (0,3,0,4,1,2)
```

Its fifteen varieties are distinct and adjacent-repeat. The [proof](FiveColour/Universal.lean)
is independent of the interval certificates: the lower bound needs three
sources of each repeated colour, and the upper bound checks one matching for
each target. The paper gives a structural Hall proof. The [construction data](data/five-colour-universal.json)
and independent physical audit include all 75 target matchings.

## Verification

The complete physical corner theorem and cuboid classification have been checked
in Lean. To reproduce the whole proof from the committed inputs:

```sh
lake exe cache get
make verify-full WORKERS=2
```

Requirements: Lean/mathlib v4.35.0, Git, Python 3.12+, Make and a C++20 compiler
with OpenMP. No SAT solver, OR-Tools or GPU is required. The toolchain and project
dependencies are pinned in `lean-toolchain` and `lake-manifest.json`.

| Command | What it establishes |
| --- | --- |
| `make verify-full` | All code audits, Lean infrastructure, all 279 certificates, the final corner theorem, unconditional cuboid results and axiom audits. |
| `make check` | Code audits and Lean infrastructure. **Partial verification:** it does not check the complete corner proof. |
| `make check-replay-data` | Regenerates in a temporary directory and compares every retained file without modifying it. Included in `check-code`. |
| `make replay-data` | Explicitly regenerates the retained Lean proof sources. Generation alone proves nothing. |
| `make replay` | Checks all generated certificates, assembles the corner theorem and audits its axioms. The generated proof sources are retained. |
| `make check-extensions` | Applies the corner theorem to all cuboid and support results. Requires completed replay. |
| `make check-classification-data` | Separately checks the 349-root route (342 exclusions and seven terminal enumerations), physical/orbit data, rejection controls and retained generated sources. |
| `make classification-replay` | Separately checks the complete 56-representative Lean classification and its axiom report. |
| `make paper` | Builds the manuscript PDF; additionally requires latexmk and LaTeX. |

Plain `make` runs the complete `verify-full` route. `make help` lists the main commands.

`verify-full` records the source revision, working-tree changes (including
removed files), source and generated-proof hashes, per-stage elapsed times, logs
and final axiom reports under ignored `build/verification/`. Before and after
verification it checks every installed dependency's HEAD, tracked bytes and file
modes against its manifest pin, rejects dirty or additional nonignored sources,
and records a SHA-256 digest of each source tree. Ignored build caches are allowed.
It also records actual tool versions and effective Make settings, including the
C++ compiler flags. Success requires unchanged project and dependency sources
and tool settings. Retained replay sources are checked before the Lean builds,
without overwriting them. It also works from an extracted review
archive, checking its source manifest. Archive a successful record with the
exact submission source; do not commit machine-local verification logs.

The unconditional publication endpoints are in [Solution.lean](Solution.lean):
`FiveColour.Puzzle.box_frame_threshold` and `complete_box_threshold`.
The corner proof is `FiveColour.Packed.ProjectedChunks.threshold15`, with
`sharpThreshold15` proving sharpness. Its generated sources are retained for clean Lake/Comparator builds and
reproducible with `make replay-data`. Audits permit only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`; the proof uses no `sorry` or `native_decide`.

The multiplicity, three-variety classification and generalized-family theorems can be checked
without generating or replaying interval certificates:

```sh
lake build FiveColour.ExtremalClassification FiveColour.ExtremalFamilyTheorems
```

## What the computer-assisted proof does

The implementation separates the [interval checker](FiveColour/BoxCertificates.lean),
[packed checker](FiveColour/PackedVerified.lean), and [chunk composition](FiveColour/PackedChunks.lean).

1. **Reduce the physical puzzle to finite constraints.** Lean verifies the
   75 cube varieties, physical corner compatibility, Hall's theorem, symmetry
   reductions and coverage by 357 integer root problems.
2. **Shrink the problems.** Proved containments and arithmetic discard 78 roots.
   A proved deletion argument reduces the budgets and sizes of the remaining
   279 problems. These are the “projected” problems.
3. **Check saved certificates.** Each certificate is a tree of interval
   refinements, exhaustive splits and contradictions. For example, a split
   checks both `x_i ≤ 2` and `x_i ≥ 3`. The checker verifies every step and that
   every branch closes. Search found the trees; verification does not rerun it.
4. **Connect the results.** Lean proves that the checker is sound, checks all
   279 certificates, and combines their exclusions with coverage. Hence a
   fifteen-cube counterexample cannot exist. The explicit fourteen-cube
   obstruction proves sharpness. Elementary cuboid deductions then apply.

“Replay” means step 3: following a saved certificate and verifying its steps.
The C++ implementation supplies a fast, independent audit. The Lean route
computes the check inside the kernel and connects it to the physical theorem;
the search and certificate exporters are not trusted.

The retained archive contains **298,167 instructions in 279 certificates**,
compressed to about 227 KiB. Lean checks them in 2,926 pieces of at most 128
instructions, with proved composition and exact boundary checks. The **357 root
definitions remain necessary**: the current proof derives its smaller cover
from them. See [data provenance](data/README.md) and the
[formalisation guide](FiveColour/README.md).

## Replay time and memory

A certificate instruction can require many large-integer operations and checks
of Hall alternatives. Kernel evaluation is substantially more expensive than
running the compiled C++ checker. Chunking bounds each computation; it does not
turn every instruction into a constant-cost primitive.

There are three different timing questions:

- **Fresh build:** checks the geometry, reductions and certificates. This is the
  meaningful cost for a new verifier, after downloading the pinned Mathlib cache.
- **Incremental build:** rechecks only changed modules and their dependants.
- **Cached rerun:** Lake validates the complete theorem's dependency traces in
  one invocation, then the axiom audit runs again. This is not a fresh kernel replay.

Defaults are two certificate workers and one Lean thread per case. Raise
`WORKERS` only when sufficient memory is available; `LEAN_NUM_THREADS` controls
shared-library and extension builds. See the [formalisation guide](FiveColour/README.md#replay-operation-and-provenance)
for cache validation, tuning, case benchmarks and resumable replay.

## Review archives and CI

```sh
python3 -S scripts/package_review.py
```

This makes a source snapshot with checksums and the pinned project dependency
under ignored `build/review/`. It records the base commit and any differences;
a dirty snapshot is not described as that commit. From the extracted archive:

```sh
sha256sum -c SHA256SUMS
python3 -S scripts/bootstrap_review.py
lake exe cache get
make verify-full WORKERS=2
```

The shared [colour-cubes-core](https://github.com/jasondavies/colour-cubes-core)
library supplies the physical model, proper rotations and generic geometry.
No companion paper's threshold theorem is imported. The dependency is bundled
as its pinned commit and complete source tree in a shallow Git bundle; Lean and Mathlib still require
installation. The generic completion argument is adapted from the companion
[four-to-three paper](https://hexagonmath.org/2611.00070v1); its provenance is
described in the paper and [formalization.yaml](formalization.yaml).

Ordinary CI runs `make check` and caches project builds. The manually triggered
[full verification workflow](.github/workflows/full-replay.yml) runs
`make verify-full` from a fresh checkout, with two workers and a six-hour limit.
Its complete run includes the unconditional cuboid results. Neither workflow
claims an external-kernel comparator pass.
The [formalisation guide](FiveColour/README.md#replay-operation-and-provenance)
describes the workflow artifacts and what to preserve for a permanent release.

## Palomar interface and external comparison

[Challenge.lean](Challenge.lean) states 15 claims using only Mathlib: the corner
threshold and sharpness, both cuboid thresholds, support thresholds, the
multiplicity bound, the five-class three-variety classification and the generalized
obstruction family, and the universal minimum and construction. It defines varieties through proper rotations,
not catalogue indices. The cuboid model specifies corners, edge positions,
face interiors and interior positions by their exposed faces.

[ComparatorBridge.lean](FiveColour/ComparatorBridge.lean) and
[SubmissionBridge.lean](FiveColour/SubmissionBridge.lean) prove agreement with
the proof models. The intentional Challenge holes are statements to compare;
the proof library does not import Challenge. All generated replay source files
are retained, so `lake build Solution` works without a separate generation step.

`make comparator` runs the complete statement comparison with Lean's kernel and
NanoDa, the two mandatory Palomar checkers. It exports the complete proof
dependency closure and checks it again, so cached Lake artifacts do not make
this comparison a cached verification.

**All fifteen claims passed on 8 November 2026.** Statements, shared definitions
and permitted axioms passed comparison, and both NanoDa and Lean's standalone
kernel accepted the complete solution export. The run took **4 h 13 min 28 s**
using validated Lake artifacts; it excludes a fresh project build.

The [comparison provenance extract](verification/optimized-comparator.json) identifies source
snapshot `060558e520c7`, the actual dependency trees, tool binaries and settings.
Its [complete output](verification/optimized-comparator-output.txt),
[resource measurements](verification/optimized-comparator-resources.txt), and
[preceding verification extract](verification/optimized-full.json) are retained.
The [publication policy](verification/README.md) distinguishes these sanitized
extracts from raw local records, identified by their checksums.
The Lean proof sources and certificate inputs match this comparison and its
preceding full verification, including the revised shared projection bridge.
The comparison overlapped other verification work; its duration is an observed
run time, not a controlled performance comparison. The complete classification
has a separate replay.
This scope excludes the separately staged complete 56-class classification and
the minimum-universal spanning-tree corollary, which is outside the comparator
interface. The corollary is included in the ordinary Lean build and axiom audit.

The narrower `make check-comparator-universal` checks the two universal claims
without the interval replay; `make check-comparator-lower` checks only the face
rule and lower bound.

## Repository and attribution

- `paper/`: manuscript source and PDF.
- `FiveColour/`: physical definitions, proof infrastructure and cuboid deductions.
- `data/`: current certificate archive, root definitions, geometry and witnesses.
- `scripts/`: reproducible serializers, independent audits and verification driver.
- `src/`: certificate checker, exporter, interval search and geometric audits.

GPT-6-Astra (OpenAI), through Codex, developed the arguments, computational
search, verification programs, Lean formalisation and manuscript under Jason
Davies's direction. Claude Opus 5.5 (Anthropic), through Claude Code,
contributed illustrations, the migration to the shared `colour-cubes-core`
library, and manuscript review and editing. The author takes responsibility
for the content; see the disclosure in the paper. Automated checks are not
independent human peer review.
