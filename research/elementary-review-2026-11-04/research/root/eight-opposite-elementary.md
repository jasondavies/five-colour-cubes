# Eight opposite-repeat cubes with multiplicity cap two

**Theorem.** Any eight opposite-repeat five-colour cubes, with no variety
occurring more than twice, assemble an opposite-repeat target.

An opposite variety is an undirected four-cycle of K5; each edge gives
both directed corner positions. This proof uses the elementary three-
pairs and neighbouring-pairs constructions in `../opposite_small_lemma/`.
It uses the line geometry from `nine-opposite-sources.md`, but does not
assume the numerical nine-source theorem or any exhaustive search.

## 1. Incidence facts and a five-source core

Every edge belongs to six opposite varieties. Every pair of distinct
edges belongs to two varieties, and is avoided by exactly five.
For a fixed target, each two-edge intersection belongs to exactly one
other variety; each one-edge intersection belongs to exactly two.

The five distinct varieties avoiding two fixed edges form a useful
core. They can fill any five corners of a suitable central target.
The following two normal forms cover adjacent and disjoint forbidden
edges. Each entry denotes a set of undirected edges.

| Forbidden pair F | Central target T | Intersections of the other four avoiders with T |
| --- | --- | --- |
| {01,02} | {13,14,23,24} | {14,23}; {13,24}; {23,24}; {13,14} |
| {01,23} | {02,03,12,13} | {12,13}; {02,03}; {03,13}; {02,12} |

Every target edge has three source neighbours. A corner set using two
edges has at least four neighbours, since only the unique variety with
the complementary two-edge intersection can avoid it. A set using
three edges sees all five sources. Hall therefore gives a matching
of any five target corners.

We need two elementary ways to fill the other three positions.

* Three distinct opposite varieties can match three corners of any
  target: each has at least two corners, and at most two varieties
  can have their entire intersection in one bidirected edge.
* Three opposite sources can also match three corners if one sees
  at least two target edges. Every two-source union has size at least
  two, while the three-source union then has size at least four.

Finally, any four-cycle containing the forbidden pair F meets its
central target T in two edges. For adjacent F, the cycle closes the
two-edge path through one other vertex, and its two closing edges
belong to T. For disjoint F, its other two edges join the two pairs
and likewise belong to T.

## 2. Zero or one doubled variety

### Eight distinct varieties

At most one undirected edge has source frequency at most one. Otherwise
two low-frequency edges would require at least5+5−2=8 omitted varieties,
whereas only seven varieties are omitted.

If the eight varieties contain all five avoiders of any two edges,
use their five-source core and the remaining three distinct sources.
Otherwise every two-edge target set has at least four neighbours:
a failure would require at least five sources avoiding those two edges.
Every three-edge target set has at least six neighbours, since only
two varieties avoid three edges of a four-cycle.

Choose a target avoiding the possible low-frequency edge. Its single
edges have at least two neighbours, its pairs at least four, its triples
at least six, and all four edges see all eight sources. These are all
Hall inequalities, proving the claim.

### One doubled variety P

Use P as target. Its own two copies satisfy the one-edge inequalities.
Any three target edges have at least six neighbours, because at most
two single varieties avoid them. Hence failure would require a pair
F⊂P having at most three neighbours. All five avoiding varieties must
then occur among the six distinct single sources.

Use their five-source core. The remaining sources are two P copies
and one single. P contains F, so it sees two edges of the central
target, by Section1. These three sources match three target corners,
and the five-source core fills the rest.

## 3. Three doubled varieties, or neighbouring doubled varieties

If at least three varieties are doubled, the three-pairs lemma assembles
using those six cubes and any two others.

If exactly two doubled varieties P,Q share two edges, the neighbouring-
pairs lemma applies to two copies of each, two further opposite sources,
and the two remaining sources.

The only remaining profile is 2P+2Q and four distinct single varieties,
with P,Q sharing exactly one edge e.

## 4. The one-edge companion is present

There is a unique variety V meeting both P and Q only at e. Normalize

    P={13,14,23,24},  Q={01,04,13,34},  V={02,03,12,13}.

Suppose V is one of the four single sources. The other three singles
are distinct and differ from P,Q,V. Consider these three targets:

| Target | P intersection | Q intersection | V intersection | V-private edge |
| --- | --- | --- | --- | --- |
| {12,13,24,34} | {13,24} | {13,34} | {13,12} | 12 |
| {03,04,13,14} | {13,14} | {13,04} | {13,03} | 03 |
| {01,02,13,23} | {13,23} | {13,01} | {13,02} | 02 |

**Claim.** Each target assembles as soon as an extra single source
contains its V-private edge.

Check source-side Hall. A union of one target edge can contain at most
two of the three extra singles and none of P,Q,V, so has at most two
sources. A union of two target edges can contain only one of the three
displayed anchor patterns. If it contains a P or Q pattern, it omits
the V-private edge and hence misses the extra source containing that
edge; it therefore contains at most two anchor copies and two extras.
If it contains the V pattern it contains at most one anchor copy and
three extras. In either case at most four sources are confined there.

A three-edge union can contain at most two anchor patterns. If they
are P,Q, it omits the V-private edge and therefore contains at most
four anchor copies and two extras. If one is V, it contains at most
three anchor copies and three extras. Thus at most six sources are
confined to three edges. All source-side Hall inequalities hold.

The only opposite varieties avoiding all three edges12,02,03 are P,Q.
Indeed those edges form the path1–2–0–3. Omitting an endpoint leaves
an internal vertex of degree one; omitting the isolated vertex4 leaves
only three allowed edges. Omitting either internal vertex gives the
unique avoiding four-cycle P or Q. Thus every extra single contains
at least one V-private edge in the table, and one target assembles.

## 5. The companion is absent

Use P as target. Single-edge Hall inequalities hold because P occurs
twice. Three-edge inequalities also hold: a three-edge complement could
have three avoiding copies only from Q,Q,V, and V is absent. Thus a
failed P target has a two-edge obstruction F⊂P∖Q, avoided by both Q
copies and at least three of the four singles.

If all four singles avoid F, they and one Q are precisely the five
distinct avoiding varieties. Their central target has a five-source
completion. The remaining sources are P,P,Q; the remaining Q sees
at least two target edges because it is one of the five avoiding
varieties. These three sources fill the other three corners.

We may therefore assume exactly three singles avoid F. Likewise, if
Q does not assemble, exactly three singles avoid a two-edge set
G⊂Q∖P. The sets F,G are disjoint, and their complement L in K5 has
six edges.

The two three-element sets of single avoiders have at least two members
in common. Thus L contains two distinct four-cycles. Their union must
have exactly six edges, and is either K4 or K2,3. It contains exactly
three four-cycles, the familiar line of opposite varieties.

There is a line target T containing both P∩L and Q∩L. Explicit normal
forms are:

| Line union L | P | Q | T | Edge h of T outside P∪Q |
| --- | --- | --- | --- | --- |
| K4 on1234 | {01,02,13,23} | {03,04,13,14} | {13,23,24,14} | 24 |
| K2,3 with parts01 and234 | {01,23,02,13} | {24,34,02,03} | {02,03,12,13} | 12 |

These are the two line normal forms justified in
`../opposite_small_lemma/nine-opposite-sources.md`, Section3.

If three single varieties avoid both F and G, all three line varieties
are present. Then 2P+2Q and those three line sources fill any seven
corners of T: a target edge has at least two neighbours, a pair has at
least five, and a triple sees all seven sources. The remaining single
completes the target.

Otherwise exactly two singles X,Y avoid both pairs. The other two,
R,S, satisfy

    R avoids G and meets F;    S avoids F and meets G.

In either normal form, the only four-cycle avoiding G and h while
meeting F is P itself. Since R differs from P, it must contain h.
For clarity, this small graph fact can be checked as follows.

* In the K4 form, avoiding G={03,04} leaves vertex0 with possible
  neighbours1,2. A cycle meeting F={01,02} must use both edges. Its
  other two edges close through3 or4; avoiding h=24 forces the
  route through3, which is P.
* In the K2,3 form, G={24,34} and h=12. A cycle using23 must also
  use02, because vertex2 then has only neighbours0,3; its only
  four-cycle closure is through13,01, giving P. A cycle using01
  must leave vertex1 through13 or14. The route through4 cannot
  return in two steps, since24,34 are forbidden; the route through3
  must use23,02. This again gives P.

Now consider the six-source core 2P+2Q+X+Y. Every source sees at least
two edges of T. Every target edge is covered by X or Y, because their
union is L. Three target edges also have P or Q copies, so their
frequencies are at least two. The remaining edge h acquires its second
neighbour from R.

A two-edge set has at least four neighbours already in the six-source
core: the only variety that can avoid it while meeting T in at least
two edges is the unique complementary-pair variety, with multiplicity
at most two. Every three-edge set sees all six core sources. All four
edges see all eight sources. Hall therefore gives a full assembly of T.

This completes all multiplicity profiles and proves the theorem.

## Consequence: seven opposite sources and any adjacent cube

**Corollary.** Seven opposite sources with multiplicity cap two, together
with any adjacent-repeat cube A, assemble an opposite target using all
eight cubes.

The directed cut of A contains the forward halves of three opposite
varieties, one for each choice of two columns. If all three varieties
are already doubled among the seven sources, the three-pairs lemma
applies, with the seventh opposite source and A as the two extras.

Otherwise choose one of these three varieties R that is not doubled.
Replace A temporarily by R. The eight opposite sources have cap two,
so the theorem supplies an assembly. Let c be the corner assigned to
the temporary R. Its underlying edge crosses the two parts of A, so
exactly one of c and its reverse belongs to A. If c belongs to A,
replace R by A directly. Otherwise reverse every directed corner
of the assignment. This preserves the target and every actual opposite
source, since their corner sets are bidirected; the reversed c now
belongs to A. Choosing compatible proper rotations realizes the new
assignment. This proves the corollary.

## Consequence: the seven-source rescue graph spans four vertices

For any seven-source opposite core with cap two, let E be the union of
corners that can be left as the sole hole in a seven-position matching
to an opposite target. E is bidirected.

Its underlying graph has a connected component on at least four
vertices. Otherwise its components can be partitioned into a set of
two vertices and a set of three. The corresponding adjacent cut would
avoid E, contradicting the preceding corollary: an assembly with that
adjacent cube must use it at a one-corner hole of the seven-source core.

In particular this provides a shorter closure of the fourteen-source
o=7 branch, and o≥8 is solved by opposite sources alone. The longer
seven-source proof is retained as an independent structural argument.
