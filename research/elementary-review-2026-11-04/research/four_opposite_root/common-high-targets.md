# A common high target for one doubled opposite variety

**Status: elementary proof; independent audit passed.** See
`common-high-audit.md` for the audit of the reductions in this note.

This note supplies the main reduction for four opposite sources
of profile 2,1,1. The source multiset is 2D+P+Q, where D,P,Q are
distinct opposite varieties. There are ten adjacent sources, each
tricoloured-corner class occurring at most three times.

An opposite source is high on target T if it meets at least two of
T's four underlying edges. Every opposite variety is high on itself.
An edge always denotes both directed corner positions unless one
direction is explicitly specified.

## 1. Three basic facts about the adjacent pool

The following statements hold in a pool with no opposite assembly.

### Nine adjacent cubes cannot all avoid two edges

If the two edges meet, a cut avoiding both must keep all three of
their vertices together. Only two reverse adjacent classes do this,
with combined capacity six, which cannot accommodate nine cubes.

If the edges are disjoint, each endpoint pair stays together. The
pairs lie on opposite sides of the cut; the fifth colour may join
either side. Thus there are four possible classes, two in each
orientation between the pairs, with capacity six per orientation.
Nine cubes split with at least three in each orientation. Four cubes
in each orientation would fill an opposite target between the pairs.
If one orientation has only three, use four cubes from the other
orientation and those three, together with any opposite source in
the remaining position. An opposite source meets that target in at
least one underlying edge and supports its required direction. Again
there is an assembly.

Consequently at least two of the ten adjacent cubes meet any pair
of underlying edges.

### Ten capped adjacent sources have matching rank at least four on any target

On a fixed opposite target, each adjacent class has a two- or four-
position intersection. At most two classes are confined to two
specified positions, and at most three to three specified positions.
These cut facts are proved in
`../four_opposite_lowrep/four-distinct-opposites.md`, Section 1.

If the ten sources had rank at most three, a Konig cover would use
at most three corner/source vertices. Three corner vertices contain
at most nine copies. Two corner vertices contain at most six copies,
and at most one other source vertex is allowed. One or no corner
vertices cannot cover ten sources, since every source meets at least
two corners. This is impossible. Hence the rank is at least four.

### Three covered underlying edges can be retained in a four-corner matching

Suppose three underlying target edges each occur in the adjacent pool.
Their one-edge neighbourhoods are nonempty. Each two-edge neighbourhood
has at least two sources by the first fact. Every adjacent source
meets the three-edge set, since it uses at least two of the four target
edges. Hall therefore matches the three edges to three distinct sources;
choose a compatible directed corner on each.

This is an independent three-position set in the adjacent matching
matroid. Since that matroid has rank at least four, extend the set to
four positions. Equivalently, augment the matching while keeping all
three positions matched. The resulting four corner positions still
use at least three underlying edges.

If all adjacent target intersections are confined to just two
underlying edges, there is already an assembly: meeting edges admit
only two classes, of capacity six; disjoint edges admit four classes
in two reverse orientations, and ten cubes force at least four in
each orientation. Those eight adjacent cubes fill the common high
rectangle of their four classes.

## 2. A fully supported common high target suffices

**Lemma.** Suppose D,P,Q are all high on an opposite target T and
their union contains every edge of T. Then 2D+P+Q and the ten capped
adjacent sources contain an opposite assembly.

Suppose, for contradiction, that no opposite assembly exists, so
the conditional facts of Section 1 apply.

If D=T, every target edge has two opposite neighbours. A two-edge
set is avoided by at most one of the single varieties P,Q, since
among varieties high on T only one can have its whole intersection
in the complementary two-edge pair. Thus any two-edge set has at
least three opposite neighbours. Any three-edge set meets all four
opposite copies.

By Section 1, choose four adjacent corners using at least three
underlying edges. Their four-position complement also uses at least
three edges, so the preceding neighbour counts satisfy every Hall
inequality for it. The four opposite cubes fill that complement.

Now suppose D differs from T. It meets T in exactly two edges.
Let F be the other two edges of T.

If an edge f of F is absent from the entire adjacent pool, use the
zero-edge lemma in
`../four_opposite_lowrep/one-double-zero-edge.md`: D avoids f, so
that lemma gives an opposite assembly.

Otherwise both F edges occur in the adjacent pool. Unless all its
target intersections are confined to F (already solved in Section 1),
a third edge occurs. Match four adjacent corners while retaining a
corner on each F edge and on that third edge, using Section 1.

The four remaining positions satisfy Hall for the opposite sources:

- A set on an edge of D has at least two neighbours.
- An edge of F has at least one neighbour by the full-support
  assumption, and at most one of its positions remains.
- Both P and Q meet F: a distinct variety high on T cannot have
  its entire intersection equal to D∩T, since that two-edge pattern
  determines D uniquely. Thus a subset meeting both edges of F has two
  neighbours, and at most two of its positions remain.
- Any other two-edge set has the two D copies and at least one of
  P,Q as neighbours. Its remaining positions number at most three,
  because the four-position complement uses at least three edges.
- A set on at least three edges meets all four opposite copies.

The opposite sources therefore fill the remaining four positions.
This proves the lemma.

## 3. A common high target always exists

**Geometric lemma.** Any three distinct opposite varieties have an
opposite target on which all three are high.

If two of the varieties are neighbours (share two edges), they lie
on a line of three four-cycles inside a K4 or K2,3. If the third
variety is on that line, any line target works. If it is outside,
it meets exactly one line target in two edges and the others in one;
choose its high line target. This is the elementary line geometry
in `../opposite_small_lemma/two-neighbouring-opposite-pairs.md`.

Moreover this target is fully supported by the first two varieties:
it is either one of them, or their symmetric difference. Consequently
Section 2 already solves every triple containing a neighbouring pair.

It remains to consider three pairwise nonneighbouring varieties.
Normalize the doubled variety and one single to

    D=O60={13,14,23,24}, P=O67={01,04,13,34}.

A variety meeting both only in one edge has exactly four possibilities:

| Other single Q | Edges of Q | A common high target | Edge of target absent from D∪P∪Q |
| --- | --- | --- | --- |
| O65 | 02,03,24,34 | O62={12,13,24,34} | 12 |
| O69 | 02,04,12,14 | O66={03,04,13,14} | 03 |
| O72 | 02,03,12,13 | O62={12,13,24,34} | none |
| O73 | 01,03,12,23 | O74={01,02,13,23} | 02 |

Here is a direct completeness check. If Q contains the common edge13,
it must avoid all other edges of D∪P, which uniquely gives O72.
Otherwise it uses one edge from D\P, one from P\D, and two edges
of the missing path1–2–0–3. Choose the latter two edges. If they
meet, closing their two-edge path through the allowed fourth vertex
gives O65 or O69. If they are disjoint, the only allowed closure
gives O73. The alternative closure in each case uses edge13, which
is excluded. The table is therefore a four-cycle classification,
not a source-inventory search.

Direct intersection verifies the three high-target conditions in
every row. The O72 row is fully supported, so Section 2 solves it.

## 4. Only two unsupported-centre geometries remain

In the other rows, one target edge f is absent from all opposite
sources. Every source meets the target in exactly two of the other
three edges. Since the three varieties are distinct, their patterns
are exactly the three pairs of those three edges.

The supported three edges form a path of length three. The doubled
source's pair is either two adjacent edges or the two end edges.
Path reversal identifies the two adjacent-edge choices. Thus there
are precisely two geometries, with convenient representatives:

| Doubled source D | Singles P,Q | Common target | Missing edge f | D's intersection with target |
| --- | --- | --- | --- | --- |
| O60 | O64,O68 | O61 | 12 | 14,23 (disjoint) |
| O71 | O61,O63 | O60 | 13 | 14,24 (adjacent) |

Separate small helper arguments close these two cases:

- `../four_opposite_lowrep/zero-center-opposite-pattern.md` treats
  the disjoint-edge pair;
- `../four_opposite_pairs/one-double-zero-edge-endpoint.md` treats
  the adjacent-edge pair.

Both component arguments have passed independent audit. Together
with the fully supported case and the global adjacent-zero-edge
lemma, they prove the full profile 2,1,1: four opposite sources of
this profile and ten adjacent sources of class cap three always
contain an opposite-target assembly. No inventory enumeration is
used in this deduction.
