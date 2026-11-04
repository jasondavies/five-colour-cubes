# Opposite-source proof checkpoint

## Update: 4 November 2026

The direct elementary proof of N₅=15 is now complete. See
`../root/fifteen-elementary-proof.md` and `../NEXT_STEP.md`.
The new uniform three-opposite/eleven-adjacent theorem closes the
last diffuse three-opposite fourteen-source branch. One-opposite
and two-opposite fifteen-source cases have also been proved.

For the shortest fifteen-source argument, totals three and four
use the new three-opposite theorem; totals five and six use the
five-opposite helper lemma, whose nine-adjacent corollary now permits
class cap three. The separate four- and six-opposite fourteen-source
theorems below remain valid but are unnecessary for that shortened
threshold proof. The global fourteen-failure identity still has
the three branches listed in the current main checkpoint.

**The remainder of this file is the previous checkpoint, preserved
as history. Its statements about global gaps are superseded by the
update above; the local theorem statements and proof descriptions
remain useful.**

## Current outcome

The capped mixed fourteen-source problem now has elementary proofs
for every opposite total **at least four**. The new four-opposite
case is closed in `../root/four-opposites-ten-adjacent.md`, including
all three multiplicity profiles under variety cap two and adjacent
class cap three. None of these claims relies on the finite eight-cube
enumeration.

Without the opposite variety cap, every fourteen-pool with at least
five opposite cubes assembles. A fourteen-failure with exactly four
opposite cubes has four copies of one variety and adjacent profile
5,5; this concentrated family is classified rather than excluded.

The shortest proved route for eventual exposition is:

1. **Eight capped opposite sources assemble.** This covers every
   fourteen-pool with at least eight opposite sources.
2. **Seven capped opposite sources and any adjacent source assemble.**
   This is a short corollary of the eight-opposite theorem and covers
   opposite total seven.
3. **Six capped opposite sources and eight adjacent sources with class
   cap two assemble.** This is the two-hole argument and covers the last
   opposite-total-six branch after adjacent concentration is removed.
4. **Five capped opposite sources and nine capped adjacent sources
   assemble.** In fact O+2A+B+C suffices for distinct classes A,B,C.
   The third A in the older grid reduction may be introduced virtually;
   if that pool assembles, a local corner-direction swap replaces one
   A with any actual helper. Otherwise the existing constructions need
   only two actual A copies and a helper outside at most two classes.
5. The earlier triple-adjacent-class arguments and mixed concentration
   results cover the remaining opposite-total-five configurations.
6. **Four capped opposite sources and ten adjacent sources with class
   cap three assemble.** Four distinct varieties reduce to central
   targets; one doubled variety uses a common-high-target lemma and
   two unsupported-edge geometries; two doubled varieties use line
   geometry or three orientations of a missing path. The last path
   case has an adjacent-target completion by repeated colours.

The complete eight-opposite and six-opposite proofs have both received
independent full audits. The six-opposite proof includes alternating-path
justification of its two-hole structure and explicit assignments in its
two final cut configurations.

## Precise remaining gap

There is no remaining large-opposite gap: all fourteen-pools containing
at least five opposite sources assemble, after combining the new theorem
with the earlier concentrated-opposite classifications.

The residual diffuse mixed totals are 1,2,3, with opposite variety
cap two and adjacent class cap three. The pure fourteen case with a
unique own-looped triple also remains open for the identity route.

The direct fifteen-cube problem has the same remaining opposite
totals 1,2,3: the concentrated opposite families are ruled out there
by deletion and divisibility. See `../root/fifteen-case-reduction.md`.

The complete stronger finite eight-cube lemma still has unproved
elementary cases. The new nine-source O+2A+B+C statement does not
assert that five opposite cubes and arbitrary three adjacent cubes
from more than one class always assemble. That stronger statement
has now been proved for the repeated-adjacent profile 2A+B and opposite
profile 2,2,1 in
`../five_opposite_profiles/two-pairs-two-adjacent-one.md`.

## Principal proof files and dependencies

| Statement | Proof note | Main ingredients |
|---|---|---|
| Two copies each of three distinct opposite varieties, plus any two sources, assemble. | `three-opposite-pairs.md` | Four-cycle geometry, Hall, and an explicit exceptional configuration. |
| Two copies each of neighbouring opposite varieties, two further opposite sources, and any two further sources assemble. | `two-neighbouring-opposite-pairs.md` | Three-pairs lemma; line geometry; six-position completion rules. |
| **Eight capped opposite sources assemble.** | `../root/eight-opposite-elementary.md` | The preceding two lemmas, five-avoider cores, spoke targets, and line geometry. No numerical nine-source theorem is assumed. |
| **Seven capped opposite sources plus any adjacent source assemble.** | Corollary in `../root/eight-opposite-elementary.md`; also explained in §1 of `six-opposites-eight-adjacent.md` | Replace the adjacent source by an eligible one of its three high opposite varieties, then reverse all corner directions if necessary. |
| **Six capped opposite sources plus eight capped adjacent sources assemble.** | `six-opposites-eight-adjacent.md` | Rank-two hole matroids, alternating reachability, the seven-source rescue property, and two explicit final cut families. |
| **Five capped opposite sources plus nine capped adjacent sources assemble; O+2A+B+C suffices for distinct A,B,C.** | `../root/five-opposites-nine-adjacent.md` | Replacement of a temporary third A copy; the existing five-opposite grid constructions; at most two classes avoid the rescue set. |
| **Four capped opposite sources plus ten adjacent sources of class cap three assemble.** | `../root/four-opposites-ten-adjacent.md` | High-rectangle replacement; central and common-high targets; line geometry; the missing three-edge path; an eleven-cube repeated-colour construction. |
| Five opposites \(2P+2Q+R\), neighbouring doubled \(P,Q\), plus \(2A+B\) with distinct adjacent classes, assemble. | `five-opposites-neighbouring-pairs.md` | Line block profiles \(111,220,222\) and direct five-position completions. |
| Five capped opposites and a triple adjacent class force a solution in a fourteen-pool when at most one opposite variety is doubled. | `five-opposites-low-repetition.md` | Grid rank cover; five-position completion after two adjacent corners are reserved. |
| The same fourteen-pool conclusion holds with two doubled nonneighbouring opposite varieties. | `five-opposites-nonneighbouring-pairs.md` | One overlapping grid shape, three disjoint grid diagrams, and rescue sets avoided by at most two classes. |

The new five-opposite theorem and the nine-source helper lemma passed
an independent mathematical audit, including every rescue set and
source allocation. See `../five_opposite_computation/five-target-proof-audit.md`.

The adjacent four-class and five-class reductions are supplied by the
separate mixed-source work. The proof dependency chain is acyclic: the
eight-opposite theorem borrows only the explicit line geometry from the
nine-opposite note, not the numerical nine-source theorem.

## Retained intermediate proofs

These notes remain valid, though the shorter route above now supersedes
some of their numerical conclusions:

* `six-opposites-three-adjacent.md`: six capped opposite sources plus
  three sources in one adjacent class assemble.
* `nine-opposite-sources.md`: nine capped opposite sources assemble.
* `ten-opposite-sources.md`: an independent, shorter ten-source argument.
* `eight-opposites-two-adjacent.md`: eight capped opposite sources plus
  two adjacent classes that are neither equal nor reverses assemble,
  deduced from the nine-source theorem by rescue sets.
* `seven-distinct-opposites.md`: seven distinct opposite varieties plus
  any adjacent source assemble, by a direct grid argument.
* `seven-opposites-seven-adjacent.md`: an independent longer closure of
  the capped fourteen-source case with seven opposites. It gives the
  weaker rescue-graph support fact used during discovery of the
  six-source argument.

## What the six-source proof establishes structurally

For a rank-six opposite target, the pairs of corners that may be omitted
form the bases of a rank-two matroid. Its nonloop set \(H\) consists of
whole bidirected edges. Alternating paths give the exact source count

\[
 |N_O(H)|=|H|-2.
\]

Failure forces every adjacent-source corner of \(H\) into a single
parallel class. If that class is bidirected, its complement in \(H\)
is one globally adjacent-zero edge with opposite frequency one. If the
class is a singleton, \(H\) consists of two edges: one globally
adjacent-zero edge of opposite frequency two, and an edge whose opposite
neighbours are among those same two source copies.

Virtual seventh sources eliminate these possibilities except for two
nonneighbouring doubled opposite varieties and two distinct singles.
The complement of the doubled varieties is a three-edge path. The
seven-source rescue property then forces the eight adjacent sources into
one of two four-class configurations, each class doubled. Both have
explicit assemblies using two copies of a doubled opposite variety and
six adjacent sources.

## Additional Hall reductions

`small-hall-obstructions.md` proves that, for fourteen sources with
adjacent class cap four and opposite-variety cap two, an opposite-target
Hall obstruction has at most five positions. It also gives the valid
sufficient condition that every target corner have degree at least four,
and a counterexample to that condition being universally available.

In the remaining all-cap-two regime with \(o\ge5\), every obstruction
has at most **four** positions. For a five-position set, if its
three-corner complement has no full bidirected edge, all opposite
sources meet the set. Otherwise at most two opposite varieties and at
most two adjacent classes fit in the complement, allowing at most eight
avoiding source copies. A deficiency would need at least ten.

If every target corner has degree at least three, the only possible
obstruction in this regime is a pair of complete bidirected target edges
whose combined neighbours are exactly three opposite source copies.

## Independent checks completed during this work

The elementary proofs above do not use these checks as premises.

* Three-pairs lemma: 286,650 labelled coarse-source tests, no exception.
* Neighbouring-pairs lemma: 2,579,850 tests, no exception.
* Six opposite sources plus three sources from a fixed adjacent class:
  28,665 capped inventories, no exception; symmetry covers all classes.
* Five opposite sources with neighbouring doubled varieties plus
  \(2A+B\), \(A\ne B\): 11,115 tests at a fixed class, no exception.

Exploratory programs and tables in this directory also include failed
shortcuts and computational observations. Only the named proof notes
are asserted as elementary results. The capped five-opposite case was subsequently settled by the
replacement argument recorded above.
