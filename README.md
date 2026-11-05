# Sharp thresholds for five-colour cube assemblies

- [Paper (PDF)](paper/five-colour-cubes.pdf) and [LaTeX](paper/five-colour-cubes.tex).
- [Physical target statements](FiveColour/Problem.lean), [fourteen-cube lower bound](FiveColour/LowerBound.lean), and [formalisation guide](FiveColour/README.md).
- [Interval checker](FiveColour/BoxCertificates.lean), [packed checker](FiveColour/PackedVerified.lean), and [chunk composition](FiveColour/PackedChunks.lean).
- [Provenance and verification scope](formalization.yaml).

**Every collection of fifteen cubes, each using all five colours of a fixed
palette, contains eight that build a five-colour target. Fourteen need not suffice.** The target
is a 2×2×2 cube with monochromatic exterior faces using all five colours.
A variety is a face colouring up to proper rotation. Collections may repeat
varieties; proper rotations are allowed and interior faces are unrestricted.

A frame consists of the eight corners and noncorner edge positions of a box.
The thresholds F₅ and G₅ count available source cubes guaranteeing a frame or
a complete box, respectively; an assembly may use fewer cubes than are available.

**Every cuboid threshold is now determined**, for side lengths a, b, c ≥ 2:

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

With at most k source varieties, the exact corner threshold is **8 for k=1,
13 for k=2, and 15 for k≥3**. Three varieties are therefore necessary for a
fourteen-cube obstruction. See [small support](FiveColour/SmallSupport.lean)
and [the 21-member obstruction family](FiveColour/MixedObstructions.lean).

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
| `make replay-data` | Generates Lean proof sources from the saved certificates. Generation alone proves nothing. |
| `make replay` | Checks all generated certificates, assembles the corner theorem and audits its axioms. Run `replay-data` first. |
| `make check-extensions` | Applies the corner theorem to all cuboid and support results. Requires completed replay. |
| `make paper` | Builds the manuscript PDF; additionally requires latexmk and LaTeX. |

Plain `make` runs the complete `verify-full` route. `make help` lists the main commands.
The earlier `projected-replay-data` and `projected-replay` names are compatibility
aliases for `replay-data` and `replay`; there is only one supported replay route.

`verify-full` records the source revision, working-tree changes (including
removed files), source and generated-proof hashes, per-stage elapsed times, logs
and final axiom reports under ignored `build/verification/`. Before and after
verification it checks every installed dependency's HEAD, tracked bytes and file
modes against its manifest pin, rejects dirty or additional nonignored sources,
and records a SHA-256 digest of each source tree. Ignored build caches are allowed.
It also records actual tool versions and effective Make settings, including the
C++ compiler flags. Success requires unchanged project and dependency sources
and tool settings. It also works from an extracted review
archive, checking its source manifest. Archive a successful record with the
exact submission source; do not commit machine-local verification logs.

The unconditional publication endpoints are in [Solution.lean](Solution.lean):
`FiveColour.Puzzle.box_frame_threshold` and `complete_box_threshold`.
The corner proof is `FiveColour.Packed.ProjectedChunks.threshold15`, with
`sharpThreshold15` proving sharpness. Its generated sources are intentionally
ignored and reproducible. Audits permit only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`; the proof uses no `sorry` or `native_decide`.

## What the computer-assisted proof does

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

The retained archive contains **499,829 instructions in 279 certificates**,
compressed to about 306 KiB. Lean checks them in 4,786 pieces of at most 128
instructions, with proved composition and exact boundary checks. The unprojected
11,599,651-instruction archive over all 357 roots, partial replay routes, duplicate
implementations and historical solver reports have been retired to Git history.
The **357 root definitions remain necessary**: the current proof derives its smaller cover
from them. See [data provenance](data/README.md) and the
[formalisation guide](FiveColour/README.md).

## Replay time and memory

A certificate instruction can require many large-integer operations and checks
of Hall alternatives. Kernel evaluation is substantially more expensive than
running the compiled C++ checker. Chunking bounds each computation; it does not
turn every instruction into a constant-cost primitive.

For cases with at least 4,096 instructions, generated replay sources use
root-specific cut lists: impossible alternatives are removed, fixed coordinates
are subtracted, and equal residual neighbourhoods are merged. Lean checks the
replacement weights and a coverage witness for every original alternative.
The resulting exclusion is transferred back to the original root problem.
Smaller cases retain the full lists because validating the reduction has an
upfront cost. The packed base remains 1024.

There are three different timing questions:

- **Fresh build:** checks the geometry, reductions and certificates. This is the
  meaningful cost for a new verifier, after downloading the pinned Mathlib cache.
- **Incremental build:** rechecks only changed modules and their dependants.
- **Cached rerun:** Lake validates the complete theorem's dependency traces in
  one invocation, then the axiom audit runs again. This is not a fresh kernel replay.

The replay driver tries Lake's `--no-build` validation of the complete theorem
first. If anything is stale or missing, it falls back to bounded parallel case
builds. Artifact existence alone never counts as verification. The record says
whether the aggregate was already cached.

Defaults are two certificate workers and one Lean thread per process. On a
machine with more memory, raise `WORKERS`; do not assume more workers are faster.
`LEAN_NUM_THREADS` separately controls shared-library and extension builds.
The replay driver always gives each case one Lean thread. Small-case benchmarks
have used several GiB per Lean process. Larger chunks can save a little time
while increasing peak memory, so the production limit remains 128.

For measurements on the retained archive, without reusing a cached case proof:

```sh
python3 -S scripts/benchmark_five_colour_replay.py --case 120 --limits 128 256 512 --repeats 3
```

To compare the original and reduced lists on the same certificate:

```sh
python3 -S scripts/benchmark_five_colour_replay.py --case 19 --limits 128 --cut-modes original reduced --repeats 3
```

A representative largest-case trial on a Ryzen 7 9700X, with 128-instruction
chunks and one Lean thread, gave:

| Case 4 (51,652 instructions) | Wall time | Peak process RSS |
| --- | ---: | ---: |
| Original cut lists, narrow imports | 34.6 min | 2.86 GiB |
| Reduced cut lists, narrow imports | 27.0 min | 3.33 GiB |

Both were fresh case checks with shared dependencies cached and passed their
axiom reports. Other checks ran concurrently; these are representative samples,
not an isolated whole-project timing. Reduction saved about 22% of both wall
and CPU time here, at a cost of roughly 0.5 GiB per process. On case 19, two
runs per mode in alternating order reduced the median from 7.8 to 6.2 minutes
(about 20%). Separately, narrowing
the imports reduced case 120's measured peak from 2.58 to 1.71 GiB with similar
runtime. Keep worker counts within the available memory.

Results include wall/CPU time and peak memory under `build/replay-benchmark/`.
These experiments reuse the shared checker dependencies and do not time a fresh
build of the whole project. Do not delete `.lake` to tidy a publication package:
it is already ignored, and deleting it removes useful dependency/build caches.

Replay progress is in `build/five-colour-chunks/ProjectedChunks/progress.json`.
Create `build/five-colour-chunks/ProjectedChunks/STOP` to stop the case workers;
remove it and rerun the same command to resume. Completed modules stay cached;
interrupted cases restart. Do not regenerate sources during replay.

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
The full workflow uploads verification records, stage and case logs, independent
audit reports and GNU time measurements as a `verification-<commit>-<attempt>`
artifact, including evidence from failed runs. Artifacts are retained for 90 days;
download the successful record for the permanent submission archive. GNU time's
maximum RSS is the largest process peak, not total concurrent build memory.

## Optional external comparison

[Challenge.lean](Challenge.lean) independently states the corner puzzle using
only Mathlib. [ComparatorBridge.lean](FiveColour/ComparatorBridge.lean) proves
agreement with the proof's model. The challenge's five intentional theorem
holes are statements to compare; the proof library does not import them.
The challenge covers the corner theorem, not the cuboid classification.

`make comparator` additionally checks the completed corner solution with the
external kernels configured by `scripts/verify-comparator.sh`. This requires a
toolchain containing those tools. A complete external comparator pass remains
unconfirmed; it is separate from successful Lean verification. The narrower
`make check-comparator-lower` checks only the face rule and lower bound.

## Repository and publication status

- `paper/`: manuscript source and PDF.
- `FiveColour/`: physical definitions, proof infrastructure and cuboid deductions.
- `data/`: current certificate archive, root definitions, geometry and witnesses.
- `scripts/`: reproducible serializers, independent audits and verification driver.
- `src/`: certificate checker, exporter, interval search and geometric audits.

The research and manuscript were developed with AI assistance under Jason
Davies's direction; see the disclosure in the paper. Author mathematical review
and submission approval are pending. Automated checks are not independent
human peer review. Before publication, freeze the source revision, run full
verification, and archive the source, manuscript and verification record with
an immutable identifier.
