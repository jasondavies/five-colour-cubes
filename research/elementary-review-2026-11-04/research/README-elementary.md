# Five-colour cubes: elementary-proof research

4 November 2026

## Current status

**The direct elementary proof of N₅=15 is complete.** Start with
[fifteen-elementary-proof.md](root/fifteen-elementary-proof.md), then
read [NEXT_STEP.md](NEXT_STEP.md) for the new lemmas, audit records,
and the exact scope of the separate fourteen-failure identity question.

This round closes one opposite plus fourteen adjacent cubes; three
opposite plus eleven adjacent cubes of class cap three; and two opposite
plus thirteen adjacent cubes of class cap three. The last result uses
a virtual-source replacement and three intersecting-cut families.
All new branches and the final joining argument have passed independent
mathematical audits. The explicit fourteen-cube obstruction gives sharpness.

The full written proof remains long and contains small displayed Hall
tables. It does not use an exhaustive inventory classification as a
premise. The global identity 3A−4B=36 for every fourteen-failure is
still open in three elementary branches and is not needed by the direct
threshold proof. No new Lean formalisation or production-repository
change is claimed.

## Earlier checkpoint (historical; superseded by the current proof)

**This is not yet a complete elementary proof of N₅=15 or of the identity
3A−4B=36 for every fourteen-cube failure.** It contains completed hand
proofs of the concentrated-opposite branch and the all-adjacent branch
with no corner-supported opposite target, together with exact checking
code. The follow-up also proves substantial concentration and support
restrictions in the outstanding branch. The global lemma itself remains
unproved at that stage. `FOLLOWUP.md` records that earlier round;
`NEXT_STEP.md` supersedes its list of open cases and the historical
open-case discussion below.

A failure means a pool from which no eight distinct physical cubes can
be assigned to the eight corners of any five-colour target cube. The
target must use all five colours. Each chosen source may be properly
rotated independently; interior faces are unrestricted.

Let g_j be the multiplicities of the twenty adjacent tricoloured-corner
classes, and let o be the total number of opposite-repeat cubes. Set

    A=Σ_j binom(g_j,2), B=binom(o,2), W=3A−4B.

The following branch classifications have hand proofs:

| Hypothesis on a fourteen-failure | Forced profile | W |
|---|---|---|
| Some opposite variety occurs at least four times | Four copies of that variety; two adjacent classes of five | 36 |
| Some opposite variety occurs three times, and none occurs four times | Three copies of that variety; adjacent classes5,3,3 | 36 |
| The tricoloured union supports no opposite target | All adjacent; classes3,3,3,3,1,1 | 36 |

The first two rows also show that all opposite sources in either row
have one variety. Their coarse geometry is forced, not merely their
numerical class-size profile.

Each permitted coarse configuration has an elementary repeated-colour
refinement classification:

| Opposite count | Adjacent sizes | Coarse labelled configurations | Failing refinements each | Total |
|---|---|---:|---:|---:|
| 4 | 5,5 | 120 | 91 | 10,920 |
| 3 | 5,3,3 | 240 | 1 | 240 |
| 0 | 3,3,3,3,1,1 | 30 | 9 | 270 |

Thus all 11,430 failures reported by the earlier exhaustive search have
an elementary explanation within these branches. **This agreement does
not establish that no other branch contains a failure.**

## The exact remaining lemma

Call an opposite target *corner-supported* when each of its eight
tricoloured corner types occurs in at least one source; these occurrences
need not use distinct source copies.

> **Unproved exhaustion lemma.** A pool of fourteen cubes is soluble
> if some opposite target is corner-supported and no opposite variety
> occurs more than twice.

This is one statement covering both outstanding regimes:

* An all-adjacent pool with a corner-supported opposite target.
* A pool containing opposite cubes, all with multiplicities at most two.

Every pool containing an opposite cube automatically has a corner-supported
opposite target. Therefore the lemma, combined with the branch proofs,
would prove the complete three-family classification and W=36. The usual
deletion argument would then prove N₅≤15: every pair survives thirteen
of the fifteen one-cube deletions, so 13W₁₅=15·36=540, impossible.

The fourteen-cube hypothesis in the missing lemma is sharp. Delete one
opposite cube from a three-opposite failure. The resulting thirteen-pool
still fails, still supports an opposite target, and its opposite
multiplicity is two.

The stronger assertion that the supported opposite target itself must
be assemblable is false. A successful proof must be allowed to construct
an adjacent target instead.

## New elementary reductions in the follow-up

These statements do not assume the exhaustive fourteen-failure list.
Full proofs and dependencies are indexed in `FOLLOWUP.md`.

* A pure fourteen-failure has maximum adjacent-class multiplicity exactly
  three, at most eight occupied classes, and at most five classes that
  occur more than once. The lower bound on the maximum uses a six-case,
  explicit Hall-table proof that nine distinct adjacent classes admit an
  opposite assembly. The four-copy and five-copy exclusions have direct
  geometric proofs.
* A three-copy class in a pure fourteen-failure either has an
  own-orientation loop or has at least two private corners. If no
  three-copy class has such a loop, every three-copy class has exactly
  two private corners in one column of its cut array.
* In a mixed fourteen-failure with every opposite variety occurring at
  most twice, all adjacent classes have size at most four. If at least
  two opposite sources occur, all adjacent classes have size at most
  three. If at least five opposite sources occur, all adjacent classes
  have size at most two.
* Any nine cubes occupying all six classes through one directed corner
  assemble. Several eight-cube configurations already suffice.
* Six distinct adjacent classes, two copies each, assemble an opposite
  target whenever their union supports one. Consequently six classes
  occurring at least twice cannot occur in a pure fourteen-failure.
* Nine opposite sources, no variety occurring more than twice, already
  assemble an opposite target. Thus a remaining diffuse fourteen-failure
  has at most eight opposite sources.

The most concentrated remaining mixed case is therefore one opposite
source with an adjacent class of size four. The small-multiplicity mixed
cases and the pure three-copy geometry remain unclosed. No conclusion
that W=36 holds globally has been added.

## Additional finite reduction, separately labelled

There is a short self-contained computer check for one further lemma:
eight cubes with at least five opposite sources, no opposite variety
occurring more than twice, have an opposite-target assembly unless
there are exactly five opposite sources and the other three sources
belong to a single adjacent tricolour class. The statement is a
necessary form for failure, not a claim that every exception fails.

The checker constructs its own geometry, uses no generated data, and
checks 757,076 eight-source completions of 106 five-opposite orbit
representatives. All 222 exceptional checks have the stated form.
It completed in about 0.1 seconds in this environment.

Together with the adjacent-class cap five (now strengthened above), this rules out a diffuse
fourteen-failure with at least five opposite cubes. Thus, if this
finite lemma is accepted, the unresolved regime has total opposite
count0,1,2,3,or4 and maximum opposite multiplicity two. This is still
not a complete proof, and the finite lemma has no hand proof yet.

See `robust_route/diffuse-eight-cube-lemma.md` and its standalone
`diffuse_eight_cube_check.cpp`. From the archive's top directory:

    c++ -O3 -std=c++20 research/robust_route/diffuse_eight_cube_check.cpp -o diffuse_check
    ./diffuse_check

## Reading order and proof dependencies

1. `root/six-adjacent-elementary.md` gives a self-contained proof that
   six copies in one adjacent corner class suffice in a fourteen-pool.
2. `root/o4-elementary.md` proves the five-opposite cap and the entire
   four-identical-opposite classification. It uses five geometric
   three-corner cover types and explicit assemblies.
3. `root/o3-covers-guide.md` indexes the complete hand proof for three
   identical opposite sources. Hall reduces it to five three-corner
   and ten four-corner geometric cover types. Each is treated by
   small Hall calculations, pigeonhole, or explicit eight-cube assemblies.
4. `support_families/elementary-support-family-proofs.md` proves the
   support-poset reduction and classifies the two pure six-cut families.
   The poset reduction is itself a hand proof; it does not depend on
   enumerating 4,231 posets.
5. `invariant_structure/elementary_refinements.md` proves the 91,1,9
   refinement counts, including the derangement description of the
   nine pure refinements.
6. `root/conflict-graph-reduction.md` gives an exact general reduction
   of repeated-colour refinements to a list-multicolouring problem.
7. `root/deletion-window.md` proves that the weaker global bound
   31≤W≤38 would already suffice. Those geometric bounds remain unproved.

Two three-opposite cover arguments use the already existing
eight-plus-three missing-pair lemma: eight sources omitting a fixed
bichromatic edge type, together with any three further sources, admit
a corner assembly. Therefore a failure of size at least eleven has at
most seven sources omitting any fixed pair. This is an elementary
lemma independent of N₅ in the current paper:

https://github.com/jasondavies/five-colour-cubes/blob/1dce44d24f76e84f0266025ab9ce0ab94a306873/paper/boxes.tex

See the lemma labelled `lem:eight-common-missing` and its preceding
signed-projection lemma. The present notes do not assume the
computer-assisted corner threshold.

## The directed-corner model

Fix colours 0,1,2,3,4. A cyclic tricoloured corner (i,j,k) is encoded by
its complementary directed pair a→b, choosing the order so that
(a,b,i,j,k) is an even permutation. A cyclic rotation of the triple
does not change this parity.

An adjacent class is a directed complete cut S→Sᶜ with |S|=2 or3.
Its pole pair P is the two-element side. Its three varieties have
repeated colour r outside P, and bicoloured corners (r,r,p), p∈P.
An opposite variety is specified by a repeated colour and a partition
of the other four colours into two pairs; its eight corners are the
two directions of the four edges between those pairs.

There are 20 adjacent classes, 60 adjacent varieties, and 15 opposite
varieties. `root/cut_model.py` implements precisely this model. The
corner sets were independently compared with all 75 physical varieties
from the repository's rotation-based geometry; the catalogue mapping
is recorded in `root/physical-map.json`.

Colour relabelling and simultaneous reflection may normalize the
whole problem. Reflection is never used as a move on an individual
source cube.

## Verification

Python 3 with only the standard library is enough for the main checker:

    python3 research/root/verify_research.py

Run it from the top directory of the extracted archive. It checks:

* The deletion-window numerical assertion on all partitions of fifteen.
* All 75 corner sets, opposite intersections, and the five/ten cover types.
* All 441 refinements of the opposite-four normal form and all 2,100
  refinements of the opposite-three normal form.
* All nine pure derangements.
* The stated Hall formulas on all 4,221 six-class profiles of size fourteen.
* The conflict-graph characterization against independent full matching
  on 360 reproducibly sampled repeated-colour refinements.

The supplementary check

    python3 research/support_families/check_o3_reverse.py

audits 2,856 eleven-source profiles in the reverse six-cut family.
The optional coarse cover checker

    python3 research/robust_route/check_o3_covers.py 15 23 27 30 51 53 54 58 102 105

reproduces the small three-opposite cover audit. It uses the proven
class/pair caps and exact matching/list colouring, and writes its
results locally. It is not an exhaustive search of the unresolved
global regime.

The hand arguments, rather than these diagnostic checks, justify the
proved branch statements. No new Lean formalisation or kernel replay
has been produced. The production repository has not been changed.

