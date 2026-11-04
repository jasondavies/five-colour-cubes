# Follow-up: elementary proofs and the remaining gap

3 November 2026

> **Historical checkpoint.** Read `NEXT_STEP.md` for the current state.
> The pure column-private case, the one-opposite four-copy case, and
> the six- through eight-opposite branches below have since been closed.
> Complete elementary proofs now cover the sharp pure-adjacent
> threshold of fifteen and eight opposite sources with variety cap two.
> The full mixed theorem and global fourteen-failure identity remain open.

## Main result and limitation

**The global identity 3A−4B=36 for all fourteen-cube failures is still
not proved elementarily.** The previous three-family classifications
remain valid, and this follow-up closes several substantial branches
of their missing exhaustion argument. It also establishes a sharp
standalone theorem:

> Nine adjacent-repeat cubes in pairwise distinct tricoloured-corner
> classes always assemble an opposite-repeat target. Eight cubes in
> distinct classes can fail to assemble any five-colour target.

Here a tricoloured-corner class consists of the three adjacent varieties
with the same six oriented tricoloured corners. The distinctness
condition concerns these twenty classes, not merely distinct physical
varieties. All assemblies use eight distinct physical cubes, with
proper rotations allowed independently.

The upper bound has an explicit six-case Hall-table proof, using five
positive cuts and four helper classes. The table contains28 obstruction
templates. Its completeness is explained by elementary Hall-set
dominance; it does not assume the exhaustive fourteen-cube classification.
The lower bound is an explicit eight-cube pool with a direct obstruction
for every possible target. See:

* `root/nine-distinct-hall-proof.md`;
* `root/eight-distinct-class-counterexample.md`.

This is a finite elementary case proof. A conceptual proof replacing
the six small Hall tables would still be a worthwhile improvement.

## 1. New pure-adjacent results

### Concentrations four and five are excluded

Any fourteen all-adjacent cubes with at least four copies in one
tricoloured class assemble. The old six-copy lemma handles larger
concentrations. The new proofs treat five and four copies by Hall
covers of the distinguished two-by-three corner array:

* `root/pure-five-class-hand.md` treats five copies;
* `pure_supported/g4-row-hand.md` treats a three-corner row cover;
* `pure_supported/g4-hook-disjoint-hand.md` treats the other two
  three-corner cover shapes;
* `pure_supported/g4-exception-hand.md` treats covers using source
  exceptions and explains completeness of the four-copy reduction.

The main tools are opposite-rectangle constructions, small Hall
inequalities, and repeated-colour incompatibilities. These are hand
arguments; the accompanying coarse enumerations served discovery and
checking roles only.

### Six doubled classes have a short structural proof

Two copies from each of six distinct adjacent classes assemble an
opposite target whenever their union supports an opposite target.
For a supported target, Hall can fail only through three corners
private to one source class. Normalizing those three corners leaves
eight possible other classes in two groups of four. Five distinct
other classes force three in one group, and four explicit constructions
finish the proof.

Using the earlier elementary support-family classification, this
implies that a pure fourteen-failure has **at most five classes that
occur at least twice**. The common-corner case is already soluble on
the twelve selected sources. In the butterfly case, any outside
source makes an opposite assembly; if all fourteen remain inside the
family, its previous classification excludes six repeated classes.

Full proof: `root/six-doubled-classes-hand.md`.

### The common-corner family has a stronger threshold

Any nine cubes occupying all six adjacent classes containing a fixed
directed corner assemble. Two eight-cube patterns already suffice:
a triple and five singletons; or doubles in two suitable classes and
four singletons. The proofs use explicit tricoloured completions and
the impossibility of six pairwise disjoint nonempty repeated-colour
sets in five colours.

Full proof: `pure_supported/common-corner-nine-hand.md`.

### Consequences for every pure fourteen-failure

Combining the preceding results gives:

1. Its maximum class count is **exactly three**.
2. It occupies **at most eight** tricoloured-corner classes.
3. **At most five** classes occur at least twice.

For the lower bound in item1, if every class count were at most two,
fourteen cubes in at most eight classes would force at least six doubled
classes, which have just been excluded.

Writing t for the number of triple classes, d for doubled classes and
s for singletons, the numerical profiles still allowed by these
three bounds alone are:

| t | d | s | 3Σ binom(g_j,2) |
| ---: | ---: | ---: | ---: |
| 1 | 4 | 3 | 21 |
| 2 | 2 | 4 | 24 |
| 2 | 3 | 2 | 27 |
| 3 | 0 | 5 | 27 |
| 3 | 1 | 3 | 30 |
| 3 | 2 | 1 | 33 |
| 4 | 0 | 2 | 36 |
| 4 | 1 | 0 | 39 |

Only the penultimate row occurs in the known exhaustive failure list.
The table is a reduction, not a proof that the other seven rows are
impossible.

### Private corners reduce the remaining geometry

For a class C of size three, call its own cut *completable after two
reservations* if, after two C cubes are removed, the other cubes can
match its six tricoloured corners. This is the own-orientation loop
condition in the conflict-graph notes.

In a pure fourteen-failure, a three-copy class that lacks this condition
has at least two corners private to that class. The proof again uses
small Hall covers and explicit substitutions into the four-copy proofs.

Full proof: `pure_supported/g3-nonprivate-hand.md`.

If no three-copy class has the completion condition, all triple classes
have private pairs. Two further hand arguments show that these are
**exactly two private corners in a column** of each class's two-by-three
array. A row pair is impossible, and then a diagonal pair is impossible:

* `root/g3-private-row-hand.md`;
* `root/g3-private-diagonal-hand.md`.

For a positive cut C(ab), a private column {ac,bc} says that every
other outset satisfies a∈S⇒c∈S and b∈S⇒c∈S. This reduces the remaining
all-private geometry to interacting two-relation orders. A proof that
these force the butterfly support is still missing. The alternative
branch containing an own-orientation looped triple is also not closed.

## 2. New mixed-pool results

Throughout this section every opposite variety occurs at most twice.
Write o for the total number of opposite sources.

### Adjacent classes of size five are excluded

Any fourteen-pool with an opposite source and an adjacent class of
size five assembles. The proof first uses disjoint-source constructions
to reduce to one opposite variety, occurring once or twice. Hall then
leaves only a row-pair or diagonal-pair corner pattern, each handled
by explicit assemblies.

Full proof: `mixed_diffuse/five-class-mixed-hand-proof.md`.

That note also contains useful independent eight-cube constructions.
For example, four copies of an adjacent class, three adjacent sources
tricolour-disjoint from it, and one opposite source always assemble.
With at least three diffuse opposite sources, a three-copy adjacent
class in a failure can have at most one disjoint adjacent source.

### Size four is excluded when o≥2

The following proof chain excludes every four-copy adjacent class
as soon as at least two opposite sources occur:

* `mixed_diffuse/four-class-four-opposites-hand-proof.md` handles o≥4;
* `mixed_diffuse/four-class-three-opposites-hand-proof.md` handles o=3;
* `mixed_diffuse/four-class-two-distinct-opposites-hand-proof.md` handles
  two distinct opposite varieties;
* `mixed_diffuse/four-class-two-identical-opposites-hand-proof.md` handles
  two identical opposite sources.

The remaining four-copy mixed case has **exactly one opposite source**.
It is not marked proved here.

### Size three is excluded when o≥5

Six diffuse opposite sources plus three copies of any adjacent class
already assemble an opposite target: nine sources suffice. The proof
uses the ranks of the three two-column rectangles, a four-position
Hall cover, and two small corner-pattern diagrams.

Full proof: `opposite_small_lemma/six-opposites-three-adjacent.md`.

For exactly five opposite sources, nine adjacent sources of class
counts at most three supply the required extra compatible corner.
All three possible opposite multiplicity profiles are handled:

* `opposite_small_lemma/five-opposites-low-repetition.md`: at most one
  doubled opposite variety;
* `opposite_small_lemma/five-opposites-neighbouring-pairs.md`: two
  doubled varieties sharing four directed corners;
* `opposite_small_lemma/five-opposites-nonneighbouring-pairs.md`: two
  doubled varieties sharing only two directed corners.

Thus any still-failing mixed fourteen-pool with o≥5 has **every adjacent
class occurring at most twice**.

### Restrictions on opposite repetitions

Two copies of each of three distinct opposite varieties, plus any
two additional cubes, always assemble an opposite target.

Also, if two doubled opposite varieties share four corners, any two
further opposite sources and any two further cubes suffice.

Full proofs:

* `opposite_small_lemma/three-opposite-pairs.md`;
* `opposite_small_lemma/two-neighbouring-opposite-pairs.md`.

Consequently a diffuse fourteen-failure has at most two doubled
opposite varieties. If o≥5 and there are two, they must share only
two directed corners. For o≥6 this follows from the neighbouring-pairs
lemma. For o=5, either two adjacent sources share a class and the
five-opposite neighbouring-pairs construction applies, or all nine
adjacent classes are distinct and the sharp nine-class theorem applies.

### Nine opposite sources already suffice

Any nine opposite-repeat sources, with no variety occurring more than
twice, assemble an opposite target. The last case has two doubled
varieties sharing one edge. If both doubled varieties fail as targets,
their two-edge Hall obstructions force three single source varieties
to be the three four-cycles in a K4 or K2,3. One of these cycles is
a common high-intersection target for the two doubled varieties.
The resulting seven-source core can fill any seven target corners,
and an eighth source completes it.

Full proof: `opposite_small_lemma/nine-opposite-sources.md`.
The simpler ten-source argument is retained in the companion
`ten-opposite-sources.md`.

Therefore a remaining diffuse fourteen-failure has o≤8. This is an
elementary upper bound; unlike the distinct-adjacent-class theorem,
no sharpness claim is made for this opposite-source bound.

## 3. Exact outstanding branches

The following table records what is still needed for the global
exhaustion lemma. These are possible regimes, not asserted failures.

| Opposite count o | Adjacent class bound in a remaining failure | Outstanding issue |
| ---: | ---: | --- |
| 0 | maximum exactly3 | A supported opposite target, with the own-loop triple or column-private geometry still unclosed |
| 1 | at most4 | The four-copy case and the smaller-class cases |
| 2,3,4 | at most3 | Exclude the remaining small-class mixed pools |
| 5,6,7,8 | at most2 | Exclude mixed pools with both adjacent-class and opposite-variety multiplicities at most2 |

The standalone finite eight-cube lemma from the previous bundle
excludes the last row computationally. It is still not available as
a complete hand proof. The present arguments close all its fourteen-pool
consequences involving an adjacent class of size at least three.

The identity W=36, the complete elementary exhaustion, and a full
elementary proof of N5=15 are therefore **not claimed**.

## 4. Checks and reproducibility

The proofs are written arguments. The exact computations are separate
sanity checks and discovery records, with no new Lean formalisation.

Run the new small certificate audit with standard-library Python:

    python3 research/root/verify_followup.py

It checks the cut-intersection bounds used in the six-doubled-class
proof, its eight short constructions, all fourteen butterfly outside
extensions, and the complete nine-class Hall certificate. The28
templates absorb96 feasible small Hall sets by set inclusion, without
enumerating four-helper inventories. It also checks the eight-class
counterexample against all75 targets and verifies its14 supported-target
Hall certificates.

Additional independent checks include all28,665 capped six-opposite
inventories for the six-opposite/three-adjacent lemma, and the small
neighbouring-pair constructions. Their C++ sources are included in
`opposite_small_lemma/`. The earlier `root/verify_research.py` remains
the audit for the previous bundle's classifications and refinements.

Exploratory JSON files are not proof assumptions. In particular the
own-loop and all-private sweeps are evidence for the next structural
lemmas, not replacements for them.

The production paper and formal proof repository have not been edited
by this research follow-up.
