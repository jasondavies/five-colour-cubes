# Four adjacent copies and two distinct opposite sources

**Status: elementary proof.**

**Theorem.** A fourteen-pool containing four copies of an adjacent
tricolour class and exactly two opposite sources of different varieties
is soluble.

The earlier nine-piece construction excludes any adjacent class of
size at least five. Suppose therefore that all adjacent classes have
size at most four, and normalize the distinguished class to A=C(01).
The notation and elementary constructions are those of the other notes
in this directory.

## 1. The Hall-cover reduction

Four A contain a same-repeat pair for the bicoloured positions of an A
target. The other two A fill two arbitrary tricoloured positions, so
the ten outside sources must have matching rank at most three on A
in a failure.

The eight-cube construction 4A+two disjoint adjacent sources+two distinct
opposite sources shows that at most one outside adjacent source is
disjoint from A.

A vertex cover of the outside/A incidence graph therefore cannot have
at most one corner vertex. With no corner vertices it would leave at
least seven disjoint sources. With one corner vertex, both opposite
sources must be exceptional source vertices, leaving at least seven
adjacent copies in the unique class meeting A in that single corner.

If the cover consists of two corners and one source vertex, the
exceptional source must be opposite: two different opposite varieties
cannot both have their A intersections in a two-corner set. The other
opposite source and all eight adjacent sources are then contained in
that pair. The thirteen-cube corollary of the five-class note solves
using four A, that one opposite source and the eight adjacent sources.

It remains that all outside incidences lie in three A corners H. The
two different opposite sources occupy different two-corner subsets of
H, so their union is H. Again H has three possible shapes.

## 2. Row triple: H={02,03,04}

The opposite sources omit colour1. Their reverse-A row0 intersections
are different two-element subsets of {20,30,40}, and hence they match
q0,r0 for any two distinct columns q,r.

Every eligible adjacent helper has at least one position q1. It has
exactly one precisely for the three classes C(02),C(03),C(04). Two
helpers therefore match q1,r1 unless both are the same one of these
classes. The eight helpers cannot all be one class, since its count
would exceed four. Choose a suitable pair of helpers and assemble
the rectangle01|qr with four A forward and the opposite sources and
helpers on its reverse half.

## 3. Column pair: H={02,03,12}

The opposite sources are

    T=opposite04∣23, omitting1;
    U=opposite02∣13, omitting4.

They can fill any prescribed two of {20,21,30}. Thus the rectangle
01∣23 solves if two helpers can fill31 and a position in {20,21,30}.

The eligible helper classes, restricted to these four reverse positions,
are

| Helper | Available reverse positions |
|---|---|
| C(234) | 20,21,30,31 |
| C(134) | 30 |
| C(04) | empty |
| C(034) | 31 |
| C(024) | 21 |
| C(23) | 20,21,30,31 |
| C(24) | 20,21 |
| C(34) | 30,31 |

Suppose some helper contains31, but the required helper pair cannot be
chosen. Hall on the two categories {31} and {20,21,30} says either no
helper meets the second category, or only one helper meets their union.
The first alternative puts all eight helpers in C(04),C(034), which
share four corners and thus have combined count at most seven. The
second leaves at least seven copies of C(04), contradicting its class
bound. Hence in a failure no helper contains31.

The helpers are therefore among

    D=C(134), R=C(04), S=C(024), Z=C(24).

Now use the rectangle01∣24: T fills20 and U fills21. D sees40, R and S
see41, and Z sees both. If both positions40,41 occur among the helpers,
two different helpers can fill them, since every helper sees at least
one and there are eight helpers. Otherwise all helpers are D, violating
the class bound, or all are R,S, violating their shared-four bound seven.

This closes the column shape.

## 4. Split triple: H={02,03,14}

The eligible opposite varieties are

    T=opposite04∣23, omitting1;
    U=opposite04∣13, omitting2;
    V=opposite04∣12, omitting3.

Any two distinct varieties match any prescribed pair from
P={20,30,41}. As in the three-opposite proof, if two helpers match a
pair from K={21,31,40}, those two helper positions and the corresponding
two P positions form the reverse half of an A rectangle, which solves.

The K intersections are:

| Helper | K intersection |
|---|---|
| R=C(04) | empty |
| D=C(123) | empty |
| E=C(034) | 31 |
| F=C(024) | 21 |
| C(234),C(23),C(24),C(34) | at least two |

If a helper from the last four classes occurs and the helpers have
K-rank at most one, all seven other helpers must be R or D. Their
counts are three and four. They are reverse cuts, so four of one,
three of the other and one opposite source solve by the elementary
4A+three-disjoint+O construction.

Thus no helper from the last four classes occurs. Nor can E and F
both occur. Interchanging2 and3 if necessary, take F absent, and write
r,d,e for the counts of R,D,E. Then r+d+e=8. Since R,E share four
corners, r+e≤7 and therefore d≥1. Since d≤4, we also have r+e≥4.

Assemble V. Four R/E sources fill their common positions
{01,02,41,42}. One A fills14. Of the remaining positions {10,20,24},
the two opposite sources fill two different ones: T sees20,24, U sees10,
and V sees all three, so any two different varieties have a two-matching.
One D fills the last position.

This proves the theorem.

## Consequence

Together with the preceding notes, every mixed fourteen-pool with an
adjacent class of size at least four is soluble whenever at least two
different opposite varieties occur. The homogeneous two-opposite and
one-opposite cases are proved in their respective companion notes.
