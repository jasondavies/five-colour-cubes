# A private adjacent column and a high opposite source

4 November 2026

**Status: elementary proof; independent root audit passed.**

## Theorem

Let A=C(01), and take three sources of class A and eleven other
adjacent sources, each tricoloured-corner class having multiplicity
at most three. Suppose none of the eleven outsiders contains either
corner 02 or 12. Adjoin the opposite source

    O=01|34={03,04,13,14},

where each undirected edge supplies both corner directions. These
fifteen sources contain an eight-source five-colour assembly.

No assumptions about own loops, private corners of other classes,
or the number of occupied classes are required. In particular, this
settles the high-intersection type of an opposite cube avoiding a
private column of an adjacent triple.

## 1. The eleven possible outsider classes

The forbidden corners 02,12 say that an outset S must satisfy
0∈S⇒2∈S and 1∈S⇒2∈S. Its size is two or three. The possible
classes besides A are exactly:

| Name | Class | Reverse-A corners |
| --- | --- | --- |
| P | C(02) | 21 |
| Q | C(12) | 20 |
| L3 | C(123) | 20,30 |
| L4 | C(124) | 20,40 |
| R3 | C(023) | 21,31 |
| R4 | C(024) | 21,41 |
| H | C(012) | none |
| B | C(234) | 20,21,30,31,40,41 |
| Z23 | C(23) | 20,21,30,31 |
| Z24 | C(24) | 20,21,40,41 |
| Z34 | C(34) | 30,31,40,41 |

Lower-case letters denote source counts. Their sum is eleven and
each count is at most three.

We use the elementary cut-containment facts already proved in
`../four_opposite_lowrep/four-distinct-opposites.md`, Section 1:
on an opposite target every adjacent cut meets two or four directed
positions; at most three classes are confined to three specified
positions, and at most two to two specified positions.

## 2. Three high targets give a short count reduction

First use target 01|23. The three A sources cover its four forward
positions, while O covers both directions of 03 and 13. This target
assembles if and only if the outsiders satisfy all three conditions:

    corner 20 is supported;
    corner 21 is supported;
    at least one of 30,31 is supported.                 (1)

Necessity follows from the single corners 20,21 and the pair 30,31,
the latter having only O as a core neighbour. For sufficiency, check
Hall. A set of reverse positions containing both 20,21 has at least
five outsider neighbours: the only classes avoiding both are H and
Z34, with combined capacity six. A reverse triple containing just
one of 20,21 has at least two outsider neighbours: the avoiders of
{20,30,31} are P,R4,H, and those of {21,30,31} are Q,L4,H.
Either list accommodates at most nine sources. All four reverse
positions have at least eight outsider neighbours, because only H
avoids them. The smaller reverse sets are handled by (1) and the
one O source.

A set meeting the forward half and meeting O has four core
neighbours, so sets of size at most four are automatic. If it avoids
O it lies in {02,12,20,21}; its only potentially deficient case is
the full four-set, which has outsider neighbours at 20,21. For sets
of five or more positions, the cut-containment bounds and eleven
outsiders give more than the required neighbours: a five-set has
at least two outsider neighbours, a six-set at least five, and
seven- and eight-sets see all eleven. This proves (1).

By exchanging 3 and 4, target 01|24 assembles under the corresponding
conditions with the last line of (1) replaced by support of 40 or41.

Suppose neither target assembles. If both 20 and 21 were supported,
no outsider could have any of 30,31,40,41. The table would leave
only P,Q,H, with capacity nine, fewer than eleven. Hence 20 or21
is unsupported. Exchange 0 and1 if necessary to assume 21 is absent.
The table then leaves only

    Q, L3, L4, H, Z34,

so

    q+l3+l4+h+z34=11.                                  (2)

Now use target T=01|34, which is O itself. On its reverse half R,
O is universal and the three A sources have no neighbours. On
its forward half the four core sources A,A,A,O are universal.
The same Hall bounds show that T assembles precisely when the
outsiders have matching rank at least three on R.

On R the remaining outsider patterns are

    Q,H: empty;  L3:{30};  L4:{40};  Z34:R.

Equation (2), together with q,h≤3, gives l3+l4+z34≥5. If z34≥3,
three universal Z34 sources give rank three. If z34=2, some L3 or
L4 is present and also gives rank three. If z34=1, then l3+l4≥4;
both are positive since each is at most three, again giving rank
three. Therefore failure forces z34=0, and (2) becomes

    q+l3+l4+h=11.

Each of these four counts is two or three, and exactly one is two.
This is the entire residual: it was derived from three target tests,
without enumerating inventories.

## 3. Explicit own loops close the residual

The class H has an own loop whenever it is a triple: after reserving
two H sources, its six corners have this matching:

    A:03,04;  L3:14,24;  L4:13,23.

All required classes have at least two copies. A triple L3 also has
an own loop in the pool containing O. Reserve two L3 sources and use

    remaining L3:34;  O:30;  A:14;  L4:20;  Q:10,24.

Similarly a triple L4 has the loop

    remaining L4:43;  O:40;  A:13;  L3:20;  Q:10,23.

If h=3, at least one of L3,L4 is a triple, and its pole pair meets
H's pole pair 34. If h=2, both L3 and L4 are triples, and their pole
pairs 04 and03 meet. Thus there are two own-loop triples with
intersecting pole pairs in every residual case.

For completeness, such a pair always assembles. An own-loop triple
in a failure must use all three possible repeated colours, since
otherwise a same-repeat pair supplies its two bicoloured target
corners and its loop finishes. The two triples' three-element repeat
sets therefore intersect. Choose a common repeated colour, reserve
one source from each class for the first class's two bicoloured
corners, using the pole shared by the two classes for the source
from the second class. Start with the first class's own-loop
matching after two of its sources were removed. Restore one of
those universal sources, and remove the chosen source from the
second class; if it was used in the matching, the restored universal
source replaces it. This completes the first adjacent target.

The contradiction proves the theorem. This final argument is valid
even when the opposite source participates in the loop matching.

## Scope

In the private-column normalization, an avoiding opposite source has
five labelled varieties and three types under the column stabilizer.
This note proves the type O=01|34. The other two types are proved in
`private-column-diagonal-opposite.md` and `private-column-row-opposite.md`.
The sole-triple predecessor is excluded by
`five-repeated-classes-two-helpers.md`; the complete one-opposite
route is joined in `one-opposite-fourteen-adjacent.md`.
