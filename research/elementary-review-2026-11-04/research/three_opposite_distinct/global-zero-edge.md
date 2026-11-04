# Three distinct opposite sources when an edge is absent from the adjacent pool

4 November 2026

**Status: elementary proof; independent root audit passed.**

**Lemma.** Three pairwise distinct opposite varieties, together with
eleven adjacent sources whose tricoloured-corner class counts are at
most three, contain an opposite assembly if the adjacent sources all
avoid both directions of any one underlying edge.

There is no condition on whether the opposite varieties contain the
avoided edge. The proof uses no inventory enumeration.

Normalize the avoided edge to 01. Its adjacent avoiders are exactly

    X=C(01), X_i=C(01i), i=2,3,4,

and their reverses. Call these the forward and backward groups. On
the forward grid

    02 03 04
    12 13 14,

X has all six positions, while X_i omits column i and contains both
other columns. An opposite source has either a two-column rectangle
or two positions in different columns; its pattern determines its
variety uniquely.

## 1. Three opposite sources and one full-column helper

**Grid lemma.** Add to the three distinct opposite grid patterns a
helper B whose grid pattern is the full grid or a two-column rectangle.
These four sources match a two-column rectangle, unless the three
opposite patterns are precisely the three pairs on three positions,
one in each column.

The full-grid matching rank is four. Source-side Hall is immediate
for subsets containing B, whose pattern has at least four positions.
Three distinct opposite patterns have union at least three, and
every one has size at least two.

Suppose no rectangle can be matched. Let M be the rank-four
transversal matroid on the six positions, and let N be its rank-two
dual. The pairs of holes that can be omitted are the bases of N.
Every same-column pair is a nonbasis. Write H for the nonloop set
of N. Alternating paths from the two holes give

    |N_sources(H)|=|H|−2.

For |H|=2, no source meets H. But its two positions belong to
different columns, since they form a basis of N; B cannot avoid
two positions in different columns. For |H|=4, B meets H, leaving
two opposite sources whose patterns are contained in the other two
positions. They would be the same variety. For |H|=5, one source
would have its pattern in the single remaining position. These
three sizes are impossible.

Suppose |H|=6. Every column's two positions are parallel in N.
The parallel classes are either the three columns separately, or
two columns together and the third separately.

In the three-class case, a two-position opposite pattern would be a
basis of N, so its complement would be matchable by all four sources
while containing no position for that opposite source. Hence all
three opposite patterns must be the three distinct rectangles.
On any rectangle, one of them and B can be taken universal by
choosing B's rectangle if B is not full; the other two opposite
sources each occupy a different whole column. They match the four
positions directly, a contradiction.

In the two-class case, let V be the single-column parallel class
and U the other four positions. Dual rank gives r_M(V)=1. There
are no M loops, because N has no coloops: each of its parallel
classes has at least two positions. Thus both positions of V are
supported, and precisely one source R meets V, containing both.
If R is opposite, it is a rectangle; B then avoids V and equals U.
If R=B, the other three sources are opposite patterns inside U.
In either case all four restrictions to U have size at least two,
their union is U, and no three restrictions lie in two positions.
For the last assertion, the opposite two-position patterns are
distinct and use different columns, whereas the restriction of a
rectangle crossing V is a single column. Hall therefore matches U,
again a contradiction.

The only remaining size is |H|=3. B meets H, so all three opposite
patterns lie in its three-position complement. A three-position
shape in two columns contains only two possible opposite patterns.
Thus the complement has one position in each column, and the
three opposite patterns are its three pairs. This proves the grid
lemma. These three varieties form a line.

## 2. A forward pool with two copies of each class

**Allocation lemma.** Three distinct opposite sources together with
two copies of each of X,X_2,X_3,X_4 contain an opposite assembly.

Among the three opposite sources choose two, U,V, and an endpoint
a of 01 such that U and V can supply incoming corners ia and ja
for different i,j in {2,3,4}. Here is why this is always possible.

Two distinct opposite varieties fail this selection only when one
omits 0 and the other omits 1. Otherwise they share an endpoint a.
If either has two neighbours of a among 2,3,4, distinct i,j can be
chosen. If both have only one such neighbour at both endpoints,
both contain 01. Their neighbours of 0 and 1 outside 01 determine
the whole four-cycle, so two distinct varieties differ at one of
these endpoints. That endpoint gives different i,j. Three distinct
varieties cannot have every pair of the exceptional omission form.

Let k be the remaining colour in {2,3,4}, and use the opposite
target with parts {a,k} and {i,j}. Put U,V at ia,ja. Its other six
positions are filled by

    X: ai,aj;  X_k: ki,kj;  X_i: ik;  X_j: jk.

Every required class count is at most two. This proves the lemma.

## 3. Both orientations occur

Choose the majority orientation as forward. It contains at least
six sources. On every high target with parts 01 and two of 2,3,4,
four forward sources match the whole forward rectangle. Each source
meets either both columns or one full column, and at most three
forward sources miss a specified column. Both columns therefore
have at least three source neighbours; Hall gives the four matches.

Choose one backward source B and identify its reverse grid with the
forward grid. If the grid lemma gives a four-source rectangle
matching, combine its three opposite sources and B on the backward
half with four forward sources on the forward half. This assembles
an opposite target.

It remains that the three opposite patterns are the three pairs on
one position in each column.

### At least two backward sources

Choose any two of them. Each has both positions in at least two
columns. Choose different columns i,j that they respectively meet,
and consider the rectangle on i,j. Put the two backward sources
in the positions complementary to the line's distinguished position
in each column. Two distinct line sources match the two distinguished
positions, because each position belongs to two of the three line
patterns. Four forward sources fill the other directed half.

This uses only two opposite sources and six adjacent sources.

### Exactly one backward source

There are ten forward sources. All four forward classes occur,
since three classes have capacity nine. Write their counts as
x,x_2,x_3,x_4. If x=1, then x_2=x_3=x_4=3; otherwise x≥2.

Up to permuting columns and interchanging the two endpoints, the
three distinguished positions have two possible shapes.

If all lie in one row, normalize them to 12,13,14. The three
opposite sources are the line of four-cycles on 1,2,3,4. Choose
k with x_k≥2, and let i,j be the other two column colours. Two
line sources can fill i1,j1 on target {1,k}|{i,j}. The remaining
six positions have the allocation in Section 2. If x≥2, use it
as written. If x=1, use an extra X_j for 1i and an extra X_i for
1j instead of the two X sources; both classes have count three.

For the mixed-row shape, normalize the distinguished positions to
02,13,14. The opposite varieties are

    O60={13,14,23,24},
    O71={01,02,14,24},
    O74={01,02,13,23}.

Use target O60. The opposite sources fill

    O74:31; O71:41; O60:23.

The adjacent sources fill

    X:13,14; X_2:24; X_3:32; X_4:42.

If x=1, replace the two X assignments by an extra X_4 at13 and
an extra X_3 at14. Both classes then use two of their three copies.
Thus this line shape is solved as well.

The sole backward source need not be used in these last constructions.

## 4. All sources have one orientation

There are eleven forward sources in four classes of cap three, so
every class has at least two copies. The allocation lemma of
Section 2 applies directly.

All orientation cases have been covered, proving the stated
global-zero-edge lemma.

## Provenance

A small exploratory check identified the line as the exceptional
grid shape. The rank-two argument in Section 1 proves that
classification directly. All subsequent allocations are explicit.
No list of eleven-source inventories or repeated-colour refinements
is used in the proof.
