# Four opposite cubes and ten adjacent cubes

3 November 2026

## Statement and scope

**Theorem.** Let a pool consist of four opposite-repeat five-colour
cubes and ten adjacent-repeat five-colour cubes. Suppose that no
opposite variety occurs more than twice, and no adjacent
tricoloured-corner class occurs more than three times. Then eight
of the cubes assemble a five-colour 2×2×2 cube with monochromatic
faces.

The target may have its repeated colour on adjacent faces. In
particular, the proof does not assert that an opposite target always
works. The final nonneighbouring-pair case uses the repeated colours
of adjacent cubes to construct an adjacent target.

This note joins the component hand proofs. The arguments use small
cut and four-cycle geometry, Hall's theorem, and repeated-colour
counting. No exhaustive inventory classification is a premise.

As throughout these notes, an adjacent class counts physical cubes
with the same six tricoloured corners, possibly different repeated
colours. Source copies used in a matching must be distinct. A corner
matching gives independently compatible proper rotations of the
chosen cubes.

## 1. Notation and the replacement construction

Use the directed-complement model on colours 0,1,2,3,4. An adjacent
class is the directed cut C(S)=S→Sᶜ, with |S| two or three. An
opposite variety is a four-cycle of K₅ and supplies both directed
corners on each of its four edges. Distinct opposite varieties share
one or two underlying edges; call them neighbours in the latter
case. Neighbouring varieties lie on a line of three four-cycles
whose union is K₄ or K₂,₃.

Two adjacent copies can be enough to exploit a repeated class.
Suppose the four opposite sources match the four positions of a
high rectangle of a class A. Together with four hypothetical A
copies they fill the corresponding opposite target. Take any two
actual adjacent helpers. Each meets at least two underlying edges
of the target, so the helpers can choose different edges. Replace
the A copies on those edges by the helpers. If a helper uses the
opposite direction, exchange the positions of that helper and its
opposite source on the same edge. Opposite sources support both
directions, so both exchanges are valid and independent.

The resulting assembly uses the four opposite sources, only two
actual A copies, and two actual helpers. This construction is used
in the distinct-source and one-double proofs to turn a repeated
class into a geometric restriction.

The allowed opposite multiplicity profiles are exactly

    1,1,1,1;  2,1,1;  2,2.

We close them in turn.

## 2. Four distinct opposite varieties

The complete proof is
[`four-distinct-opposites.md`](../four_opposite_lowrep/four-distinct-opposites.md).

If nine adjacent classes occur, the earlier nine-distinct-class
theorem already gives an opposite assembly. Otherwise choose a
class A occurring at least twice. Its six-corner grid has two rows
and three columns. Each opposite variety cuts out either a full
two-column rectangle or two positions in different columns.

If a high rectangle is matchable by the four opposite sources,
the replacement construction finishes. Otherwise consider the pairs
of grid positions that can be left empty by a four-source matching.
They form the bases of a rank-two dual transversal matroid. The
alternating-path identity

    |N_O(H)| = |H|−2

for its nonloop set H reduces four distinct source patterns to two
possibilities: they lie in a four-position shape of column sizes
2,1,1, or three of them form a line on three positions in different
columns. The proof explicitly rules out every other size of H.

Both configurations have a central opposite target T such that
every source meets at least two target edges and every edge has at
least two source neighbours. The four opposite sources then fill
any four target positions that use at least three underlying edges.

Two A copies and two actual helpers can occupy such a four-position
set. Failure of that helper selection would confine all ten adjacent
sources to three directed positions, or to two underlying edges.
The former admits at most three classes, hence nine copies. The
latter either admits at most six copies or already supplies eight
adjacent cubes assembling another opposite target. This proves the
four-distinct case.

## 3. One doubled opposite variety

Write the source multiset as 2D+P+Q, with D,P,Q distinct. The main
reduction is
[`common-high-targets.md`](../four_opposite_root/common-high-targets.md).
Call a source high on T if it meets at least two of T's edges.

Any three distinct opposite varieties have a common high target.
If any pair are neighbours, their line gives such a target whose
four edges are all supported by the three varieties. If all three
are pairwise nonneighbours, normalize D and P. Closing a four-cycle
using two edges of a three-edge missing path leaves exactly four
possibilities for Q. The note displays all four and an appropriate
common high target for each.

A fully supported common high target suffices. Ten adjacent sources
with class cap three have matching rank at least four on every
opposite target. In an assumed failure, nine of them cannot avoid
two underlying edges: the allowed cuts either have capacity at most
six or give a direct opposite assembly. These facts let us retain
three specified covered edges while extending to a four-corner
adjacent matching. The four opposite sources fill its complement
by Hall's theorem.

There is one additional case within this argument: an edge avoided
by D may be absent from the entire adjacent pool. It is settled by
[`one-double-zero-edge.md`](../four_opposite_lowrep/one-double-zero-edge.md).
Avoiding both directions of an edge leaves only eight adjacent
classes in two orientations. If both orientations occur, a grid
cover gives a high-rectangle matching or a line inventory. If only
one occurs, the ten capped sources occupy all four classes, and the
note supplies direct assignments. The line corollary used here is
proved independently in the neighbouring-pair note.

The remaining common targets have one edge absent from all three
opposite varieties. Their supported edges form a three-edge path,
and the three varieties meet it in its three possible pairs. There
are just two marked geometries: the doubled variety uses adjacent
edges of that path, or its two end edges. They are completed by:

- [`one-double-zero-edge-endpoint.md`](../four_opposite_pairs/one-double-zero-edge-endpoint.md),
  for the adjacent-edge pair;
- [`zero-center-opposite-pattern.md`](../four_opposite_lowrep/zero-center-opposite-pattern.md),
  for the disjoint end-edge pair.

The first uses explicit high-rectangle assignments and two helper
counts. The second reduces repeated classes to two possibilities
and gives two target choices for each; a fourteen-row table of
individual cuts checks that any two distinct helper classes work
on one of those targets. This is a table of directed cuts avoiding
one corner, not a table of cube inventories.

Thus the profile 2,1,1 is completely covered.

## 4. Two doubled neighbouring varieties

The stronger eight-source result in
[`neighbouring-pairs-four-classes.md`](../four_opposite_pairs/neighbouring-pairs-four-classes.md)
says that 2P+2Q, for neighbouring P,Q, plus one cube from each of
any four distinct adjacent classes already assemble.

The three line targets have three two-edge blocks. An adjacent cut
has block counts 111, a permutation of 220, or 222. Elementary
allocations always put the four distinct adjacent sources at two
positions in each of two blocks. The two opposite pairs fill the
remaining positions. Since ten adjacent sources with cap three
occupy at least four classes, this proves the required case.

The same proof works for any four opposite sources with variety cap
two drawn from one line, including profile 2,1,1. This is the line
corollary used in Section 3.

## 5. Two doubled nonneighbouring varieties

Normalize

    P={01,02,14,24}, Q={01,03,12,23}.

The complement of P∪Q in K₅ is the path 0–4–3–1. The first
reduction is proved in
[`missing-path-and-two-orientations-hand.md`](../four_opposite_computation/missing-path-and-two-orientations-hand.md).

If adjacent sources provide both directions of an edge of that
path, choose them at those two corners of a suitable target. The
four opposite sources fill any four of its other six positions;
two more distinct adjacent helpers provide the remaining two.
Failure therefore forces the whole adjacent pool to avoid one
direction on each path edge.

Up to path reversal and simultaneous direction reversal, there are
three orientations of the missing path: monotone, one change, and
alternating. The first two give opposite assemblies by the explicit
cut lists and Hall allocations in that note.

For the alternating orientation, the allowed cuts are eight classes.
Two four-corner matching tests on P and Q force all unresolved
adjacent count vectors to consist of three triples and a singleton,
in four displayed forms. The proof is
[`alternating-path-family.md`](../four_opposite_pairs/alternating-path-family.md).
Up to symmetry, each contains the eleven-source core

    P+2Q+3C(04)+3C(14)+2C(014).

This core always assembles an adjacent target. After two C(04)
sources have been reserved, its six tricoloured corners are matched
by

    P:41; Q:01,03; C(014):02,42; C(14):43.

After two C(14) sources have been reserved, that class's six
tricoloured corners are matched by

    remaining C(14):40; Q:10,12; P:42; C(014):13; C(04):43.

If either triple repeats a repeated colour, its corresponding
matching completes an adjacent target immediately. Otherwise the
repeated colours in C(04) are 1,2,3, and those in C(14) are 0,2,3.
Reserve the C(04) cube repeating 2 at the bicoloured corner (2,0)
and the C(14) cube repeating 2 at (2,4). These are precisely the two
bicoloured corners of a C(04) target repeating 2. The first displayed
matching fills its six tricoloured corners, using a different C(14)
source. All eight sources are distinct.

This contradiction closes the last pair case and proves the theorem.

## 6. Consequences and remaining gap

Combining this theorem with the earlier concentration results:

1. A fourteen-cube failure containing exactly four opposite cubes
   has all four in one variety and adjacent class profile 5,5.
   This does not say that all fourteen-pools with four opposite
   cubes assemble: the concentrated 4+5+5 failures do exist.
2. Every fifteen-cube pool containing at least four opposite cubes
   now has an elementary existence proof. For exactly four, remove
   one adjacent cube after applying the already proved multiplicity
   reductions, then use this theorem. Concentrated opposite cases
   are excluded by the earlier deletion-and-divisibility argument.
3. A hypothetical fifteen-cube failure is now restricted to one,
   two, or three opposite cubes, each variety occurring at most
   twice and each adjacent class at most three times. The pure
   fifteen-cube case was already proved.

For the fourteen-failure identity, the new four-opposite
classification gives

    A=binom(5,2)+binom(5,2)=20,
    B=binom(4,2)=6,
    3A−4B=36.

The diffuse fourteen-pool cases with one, two, or three opposite
cubes still need an elementary exhaustion. The pure fourteen case
with a unique own-looped triple also remains for the identity route.
Thus this is not yet a complete elementary proof of N₅=15 or of
the global identity.

The next uniform fourteen-cube target is three opposite cubes plus
eleven adjacent cubes, with variety cap two and class cap three.
The weaker three-plus-twelve statement would suffice for that row
of the direct fifteen-cube route.

## 7. Verification and provenance

All component geometric proofs received independent mathematical
review. The final common-high-target audit is recorded in
`../four_opposite_root/common-high-audit.md`. Diagnostic matching
programs and their outputs are retained alongside the relevant
notes. They were used to find or check small geometric assertions;
the written proof chain above supplies the exhaustion arguments.

No new Lean formalisation has been made. The production repository
at commit 1dce44d24f76e84f0266025ab9ce0ab94a306873 remains unchanged.
