# Independent audit of the one-double common-high reduction

3 November 2026

**Result: passed.** The argument in `common-high-targets.md` correctly
reduces four opposite sources of profile 2,1,1, together with ten
adjacent sources of class multiplicity at most three, to the two
explicit unsupported-centre configurations. Its fully supported
common-target lemma is valid. Combining it with the separately audited
two exception notes closes the profile 2,1,1.

This audit checked the mathematical reductions, source counts, Hall
inequalities and completeness of the four-cycle classification. It did
not run an inventory enumeration and does not use the computational
failure catalogue as a premise.

## 1. The small geometric facts being used

An adjacent cut meets an opposite four-cycle in two or four directed
positions, on distinct underlying edges. The two-position and
three-position containment bounds in
`../four_opposite_lowrep/four-distinct-opposites.md`, Section 1, are
valid: at most two classes fit in a specified pair of positions, and
at most three fit in a specified triple. For the latter bound,
suppose a triple contains reverse directions on one edge. If the
third position is on a meeting edge, at most two directed stars are
possible, each determining one class. If it is on a disjoint edge,
it can pair with at most one of the reverse directions, giving at
most two classes. Otherwise the three underlying edges form a
three-edge path. A valid end-edge pattern gives two classes and
allows at most one of the two middle-edge stars; if it is invalid,
only the two stars remain.

Two distinct opposite four-cycles share one or two edges. For a fixed
target, a prescribed two-edge intersection determines the other
variety uniquely. If those edges meet, the second cycle closes their
two-edge path through the fifth colour; closing it through the other
target vertex gives the target itself. If they are disjoint, the
non-target cycle is the other four-cycle through those two edges on
the same four vertices. This justifies every uniqueness count in the
Hall arguments below.

## 2. Nine adjacent avoiders of two edges

The argument is correct under the standing contradiction hypothesis
that the pool has no opposite assembly.

For two meeting edges, their three endpoints must stay together in
an avoiding cut. Only two reverse classes are possible, so their
combined capacity is six.

For two disjoint edges, their endpoint pairs must stay together and
lie on opposite sides of a cut. There are two classes in each of two
orientations, hence capacity six per orientation. Nine avoiders force
at least three in each orientation. If both have four, eight adjacent
sources fill the target between the endpoint pairs. In the remaining
6+3 split, use four majority sources, all three minority sources, and
one opposite source. That opposite source meets the target in at
least one edge; put it in the minority direction on that edge, and
let the three minority sources fill the other three positions.

Consequently at least two of the ten adjacent sources meet any given
pair of edges. No assumption on their repeated colours is needed.

## 3. Rank four and retention of three covered edges

The Konig-cover proof of rank at least four is valid. A cover of size
at most three with three corner vertices could cover at most nine
sources; with two corner vertices and one source vertex, at most
seven; with at most one corner vertex, every source needs its own
source vertex because each has at least two positions. Each case is
incompatible with ten sources.

For three covered underlying target edges, their one-edge
neighbourhoods are nonempty, their two-edge neighbourhoods have size
at least two by Section 2, and their three-edge neighbourhood is all
ten sources. Thus Hall matches those edges to distinct sources.
Choose a directed corner on each. The three positions form an
independent set in the transversal matroid on target positions.
Augmenting to rank four keeps those three positions matched, although
their assigned sources may change. This is exactly the retention
property required later.

If all adjacent target intersections use only two underlying edges,
the stated separate assembly is valid. Meeting edges permit only two
classes; disjoint edges permit four classes in two reverse groups,
each of capacity six. Ten sources force four in each group, and those
eight fill the common high rectangle. This alternative is needed
when selecting a third covered edge.

## 4. The fully supported common-high-target lemma

For D equal to the target, every edge has at least two opposite
neighbours, every two-edge set at least three, and every three-edge
set all four. The uniqueness fact in Section 1 permits at most one
of P,Q to avoid any two-edge set. Four adjacent positions using at
least three underlying edges leave a four-position complement also
using at least three edges. Hall then matches that complement.

For D different from the target, let F be the two edges not seen by
D. A globally adjacent-zero edge in F is covered by the independently
proved zero-edge lemma, whose doubled variety also avoids that edge.
Otherwise reserve adjacent positions on both F edges and on a third
edge, extending to four as above. In the residual four positions:

* one D edge has at least two opposite neighbours;
* one F edge has at least one neighbour and at most one position;
* the two F edges together have both P,Q as neighbours and at most
  two positions;
* any other two-edge set has the two D copies and at least one of
  P,Q as neighbours, and at most three residual positions;
* a set using at least three edges meets all four opposite copies.

These exhaust the Hall inequalities. P and Q both meet F because a
distinct high variety cannot have exactly the same two-edge target
intersection as D.

One wording correction was applied to the proof note: “a subset
supported on F has two neighbours” is now “a subset meeting both
edges of F has two neighbours”. A subset on just one F edge can
have only one neighbour; it is correctly handled by the preceding
one-edge bullet. This was a local phrasing issue, not a missing case.

For exposition, the proof may explicitly begin “Suppose, for
contradiction, that no opposite assembly exists.” Section 1 already
states this standing hypothesis, and the logical use is valid.

## 5. Common targets and the complete four-row reduction

If a neighbouring pair occurs, its line consists of three cycles
whose union is K4 or K2,3. An outside variety is high on exactly one
of these line targets. That target is covered by the neighbouring
pair, whether it is one of the pair or their symmetric difference.
Thus the fully supported lemma applies. Only line geometry is used
here, not the numerical theorem of the older neighbouring-pairs note.

For a pairwise nonneighbouring triple, colour relabelling can put

    D={13,14,23,24}, P={01,04,13,34}.

Their common edge is 13, and the missing edges are the path
12,02,03. The normalization follows directly from their different
omitted vertices: the two four-cycles share three vertices, and their
three-edge paths joining the common edge's endpoints must put the
third common vertex next to opposite endpoints, or a second common
edge would result.

If Q contains 13, it must use all three missing-path edges, giving
O72. Otherwise Q uses one D-private edge, one P-private edge, and two
of the three missing-path edges. The three choices close as follows:

| Missing-path edges chosen | Required private edges | Result |
| --- | --- | --- |
| 02,03 | 24,34 | O65 |
| 02,12 | 04,14 | O69 |
| 03,12 | 01,23 | O73 |

The other closure in each row uses 13 and the remaining missing-path
edge, and is excluded in this case. Hence the four rows are complete.
Direct intersection gives the common high targets and missing edges
displayed in `common-high-targets.md`. The O72 row is fully supported.

## 6. Exactly two unsupported-centre geometries

For each of the other three rows, the common target has one absent
edge. The remaining three edges form a path. The three opposite
varieties have the three distinct two-edge patterns in that path;
each pattern determines its variety uniquely. The doubled pattern
is therefore either the two end edges or an adjacent pair, with
path reversal identifying the two adjacent-pair choices. There is
no further choice of source variety hidden in this classification.

The representatives in the proof are correct:

| Type | Double | Singles | Target | Absent edge |
| --- | --- | --- | --- | --- |
| End-edge pair | O60 | O64,O68 | O61 | 12 |
| Adjacent pair | O71 | O61,O63 | O60 | 13 |

For additional clarity, the O65 row of the preceding table maps to
the first representative by swapping colours 3,4. The O69 row maps
to the second by the relabelling (0,1,2,3,4)→(3,4,0,1,2). The O73
row maps to the second by (0,1,2,3,4)→(3,2,1,4,0), interchanging
the names of the singles if necessary.

The two exception notes are:

* `../four_opposite_lowrep/zero-center-opposite-pattern.md`;
* `../four_opposite_pairs/one-double-zero-edge-endpoint.md`.

Their hypotheses match these representatives exactly and impose no
extra assumption about the adjacent sources avoiding the absent
edge. Their separate root audits were already completed; their
statements and independence were checked again for this reduction.

## 7. Dependency and scope check

The dependency chain is acyclic. The fully supported lemma uses the
small cut facts in the four-distinct note and the global zero-edge
lemma. The latter uses the independent four-source line corollary,
which follows from the explicit two-block adjacent allocation proof.
The exceptional notes use high-rectangle replacement and direct
helper allocations. None assumes the one-double conclusion, the
full four-opposite theorem, N5=15, or the fourteen-failure identity.

The audit establishes the one-double reduction and its assembly
with the already audited exception notes. It is not a new Lean
formalisation and makes no claim that the remaining totals of one,
two or three opposite sources have been solved.
