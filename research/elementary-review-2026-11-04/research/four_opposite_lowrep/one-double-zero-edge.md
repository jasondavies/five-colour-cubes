# A globally adjacent-zero edge with one doubled opposite variety

**Status: elementary proof; independent audits passed.**

**Lemma.** Let the opposite sources be 2D+P+Q, where D,P,Q are
three distinct opposite varieties. Suppose ten adjacent sources,
each class occurring at most three times, all avoid both directions
of an edge f. If D avoids f, the full pool has an opposite assembly.

The four-source line corollary in
`../four_opposite_pairs/neighbouring-pairs-four-classes.md` is used:
four capped opposite sources on a line, together with four distinct
adjacent classes, assemble. Ten adjacent sources with class cap three
always supply four distinct classes.

Normalize f=01. A cut avoiding both directions of 01 keeps 0 and 1
on the same side. There are exactly eight such adjacent classes:

    X=C(01), X_i=C(01i) for i=2,3,4,
    and their four reverse classes.

Call X,X_2,X_3,X_4 the forward group, and their reverses the backward
group. Reversing every corner direction permits interchange of the
groups without changing any opposite source or target.

## 1. Both orientations occur

Choose the group with at least five actual sources as the forward
group, and choose one actual source B in the backward group.

For every high target with parts 01 and two of 2,3,4, at least five
forward sources with class cap three match all four forward positions.
Each forward source has either the whole two-column rectangle or one
full column as its target intersection. At most three copies can
miss either column, so both columns have at least two source
neighbours. Hall gives the four-position matching.

On the reverse grid (identified with the forward grid by reversing
directions), B has either all six positions or a full two-column
rectangle. We claim that the four opposite sources and B match a
high rectangle unless 2D+P+Q is a line inventory.

Suppose no rectangle has matching rank four. A matching to five grid
positions would contain a matching to a complete rectangle, so the
five sources have grid rank at most four. Hall gives a set H with

    |H| + #{sources whose grid pattern is not contained in H} ≤ 4.

For |H|≤1, none of the four opposite patterns fits inside H, so the
inequality fails. For |H|=2, at most two opposite copies can fit
inside H, while B cannot; at least three sources lie outside, again
impossible. Hence |H| is three or four.

If |H|=3, B is outside H, so all four opposite patterns lie inside H.
A three-position shape in only two columns supports at most two
varieties, allowing at most three sources when only one variety is
doubled. Therefore H occupies three distinct columns and its three
two-position patterns are the line varieties D,P,Q.

If |H|=4, all five sources must lie inside H. Thus B cannot be the
full six-position class; its rectangle must be exactly H. The four
opposite patterns are contained in this rectangle. These five sources
match all four positions of H: B is universal; a deficient pair
would require all four opposite copies to lie in its complementary
two-position set, contradicting the variety cap; a deficient triple
would require three opposite patterns to fit in one position; and
single-position inequalities follow from B. This contradicts the
assumption.

Consequently the reverse rectangle matching exists, or the sources
form a line. In the former case combine it with four forward
sources to assemble; all these actual sources are distinct. In the
line case use the established four-distinct-adjacent line corollary.

## 2. All ten adjacent sources have the same orientation

After reversal if necessary, the only occupied classes are
X,X_2,X_3,X_4. Each occurs between one and three times: omitting
one would give total capacity only nine. Write their counts as
x,x_2,x_3,x_4.

Since D avoids 01, either D omits one of 0,1, or it contains both
and puts them in the same part of its bipartition. These exhaust
the possibilities for a four-cycle avoiding 01.

### 2.1 D omits one endpoint of 01

Interchange 0 and 1 if needed, so D omits 0. Write its parts as

    {1,i} | {j,k}, where {i,j,k}={2,3,4}.

The adjacent target intersections are

    X:   1j,1k;
    X_i: 1j,1k,ij,ik;
    X_j: 1k,ji;
    X_k: 1j,ki.

If x_i≥2, put the two D copies at j1,k1. Use one X_j at ji,
one X_k at ki, and two X_i at ij,ik. Two further adjacent sources
fill 1j,1k. If x≥2, use two X. If x=1, the other three counts
must all be three, so the unused X_j and X_k provide these two
positions. Thus six adjacent sources complete the target.

If x_i=1, the other three counts are all three. Choose any one of
the extra opposite sources, say P. It meets D in at least one
underlying edge. The two D copies and P can fill j1,k1 and one
of ij,ik:

- if P contains 1j or 1k, put P at that edge's incoming corner;
  the two D copies fill the other incoming corner and one of ij,ik;
- if P contains ij or ik, put it at that forward corner and put
  the two D copies at j1,k1.

The single X_i fills the other corner of ij,ik. One X_j fills ji,
one X_k fills ki, and two X fill 1j,1k. This uses three opposite
and five adjacent sources and completes D.

### 2.2 D contains both endpoints of 01

Then D is a high rectangle with parts 01 and two of the other
colours. Its two copies can match any two underlying target edges.
The sources P,Q match two distinct remaining edges unless their
intersections with D are both the same one-edge set. In the ordinary
case, match P,Q to two distinct edges and D,D to the other two.
The four actual opposite sources fill one direction on every edge;
four forward sources fill the other directions by the five-source
forward matching observation of Section 1.

For the sole exceptional shape, normalize D to the rectangle
01|23 and its common intersection with P,Q to edge 02. The only
two distinct varieties meeting D only in edge 02 are

    P={02,04,23,34},   Q={01,02,14,24}.

Use instead the high target 01|34. Its four underlying edges can
be assigned by

    D:03; D:13; P:04; Q:14.

Choose the reverse directions for the four opposite sources and
use four forward adjacent sources on the forward half. This is
again an assembly.

All cases are now covered, proving the lemma.

## 3. The one-double four-position grid-cover consequence

This records why the lemma is useful for the main four-opposite
problem. Suppose a doubled actual adjacent class A has its four
opposite grid patterns inside a four-position shape of column sizes
2,1,1. Let T be the central target determined by the singleton-column
positions. As in the earlier central-target diagrams, every opposite
source meets T in at least two edges and A∩T={a,b}.

If D=T, each target edge has two neighbours from D,D, and every
two-edge set has at least three opposite neighbours, since its
unique avoiding variety cannot be D. The central-target completion
argument in `four-distinct-opposites.md`, Section 2, applies with
these Hall bounds unchanged.

Otherwise D meets T in two edges and contains exactly one of the
two corners a,b. Let F=T\D, a two-edge set. Exactly one of a,b
lies on F. Let f be its other edge, which has no A corner.

If any actual adjacent source has a corner on f, use two A copies
at a,b and two distinct adjacent helpers, one on f. Such a pair
of helper assignments exists by the same three-position capacity
argument in Section 2 of `four-distinct-opposites.md`: at most three
classes, hence at most nine sources, can be confined to three
target positions.

The four reserved adjacent corners meet both edges of F and use at
least three underlying edges. The four opposite sources fill the
remaining four positions by Hall. Every edge in D has at least two
neighbours. Each edge of F has at least one neighbour, and has lost
at least one of its two positions to the adjacent sources. The set
F has two opposite neighbours, and has lost at least two positions.
Every other two-edge set has at least three neighbours, while the
remaining four positions cannot lie on only two edges. Every
three-edge set sees all four sources. These are all inequalities.

Thus failure forces all ten adjacent sources to avoid f. The doubled
variety D also avoids f, so the zero-edge lemma just proved gives
an assembly. This closes the four-position grid-cover branch for
opposite profile 2,1,1.
