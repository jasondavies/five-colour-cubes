# A zero-edge common high target: the opposite-pattern double

**Status: elementary proof; independent root audit passed.**

This treats the exceptional one-double core

    2D + P + Q,
    D=O60={13,14,23,24},
    P=O64={02,04,23,34},
    Q=O68={01,03,14,34},

together with ten adjacent sources of class multiplicity at most
three. Edges denote both directed corner positions.

The common high target is T=O61={12,14,23,34}. Edge12 is absent
from all opposite sources, and D meets T in the opposite pair
of edges14,23. The other zero-edge orbit, where the doubled source
meets the common target in adjacent edges, is handled separately.

## 1. If both directions of 12 occur, the target O61 assembles

The four opposite sources can fill any four of the six positions
on edges14,23,34. Each source sees two of those three edges;
each edge has at least two neighbours; and any pair of edges sees
all four sources. Hall gives the claimed four-position completion.

If adjacent sources can fill12 and21, choose two distinct actual
cubes there. The eight other adjacent sources each have at least
one target position outside edge12. They can match two distinct
such positions. Otherwise all eight would have their intersections
outside12 confined to one corner c. Their full target intersections
would lie in {12,21,c}, which supports at most two adjacent classes
and therefore at most six source copies under the class cap.

Use those two extra adjacent sources and fill the remaining four
positions with the opposite sources. Hence a failure must miss one
direction of12. By reversing all corner directions, suppose every
adjacent source avoids12.

## 2. Only four classes can be repeated

The following high-target edge matchings use all four opposite
sources. Each entry is an undirected target edge; choose all reverse
directions when an adjacent class supplies its forward half.

| Target | First D | Second D | P | Q |
|---|---|---|---|---|
| O60=12\|34 | 13 | 24 | 23 | 14 |
| O63=02\|34 | 23 | 24 | 04 | 03 |
| O66=01\|34 | 13 | 14 | 04 | 03 |
| O71=04\|12 | 14 | 24 | 02 | 01 |
| O74=03\|12 | 13 | 23 | 02 | 01 |

If an adjacent class has one of these targets as a high rectangle
and occurs at least twice, use its two copies and any two actual
adjacent helpers. The two helpers choose two different underlying
target edges; put the class copies on the other two edges and use
the displayed opposite edge matching in the compatible directions.
Thus such a repeated class already gives an assembly.

The high classes of the five displayed targets have pole pairs
01,02,03,04,12,34. Consequently a still-failing repeated class has
pole pair13,14,23, or24. Avoiding corner12 further leaves precisely

    C(024), C(023), C(23), C(24).

The ten adjacent sources with cap three occupy at least four classes.
If no class repeats, nine of them already assemble by the
nine-distinct-class theorem. Choose a repeated class A. We have
two actual A copies and can choose two helper sources B,C from
different classes, both different from A.

The operation that interchanges1 with2 and3 with4 and then reverses
all directed corners preserves this opposite core and the absent
corner12. It exchanges C(023) with C(23), and C(024) with C(24).
It is therefore enough to treat A=C(23) and A=C(24).

## 3. Four two-hole completion rules

Use the indicated two A copies. The possible holes for the two
adjacent helpers have the following descriptions. A pair is usable
exactly when its two positions lie in different displayed groups.

| A | Target | A positions | Hole groups |
|---|---|---|---|
| C(23) | O63 | 30,24 | X={23,32,42}; Y={04}; Z={40} |
| C(23) | O71 | 20,24 | X={14,41,42}; Y={01}; Z={10} |
| C(24) | O63 | 23,40 | X={03,30}; Y={04,24,32,42} |
| C(24) | O74 | 20,23 | X={01,10}; Y={02,13,31,32} |

Here are direct matching proofs of all four rules.

For C(23) on O63, Q is forced to03 after A uses30. The remaining
three opposite sources are D,D,P on the five-position set X∪Y∪Z.
The D copies see all three X positions, while P sees Y,Z and two
of the three X positions. They fill a three-position complement
exactly when the two holes are not both in X. If one hole is in X,
put P in the unremoved singleton group and use D,D on the two
remaining X positions. If the holes are Y,Z, put P at either of
its X corners and D,D at the other two.

For C(23) on O71, P is forced to02 after A uses20. The remaining
sources D,D,Q have precisely the same structure on the second
row's groups, so the same proof applies.

For C(24) on O63, Q is confined to X={03,30}. On Y, the two D
copies see {24,32,42}, while P sees {04,32}. They fill any three
of the four Y positions: if04 is present, put P there; if04 is
absent, put P at32. The D copies fill the other two. Thus exactly
one hole must lie in X and one in Y, and every such pair works.

For C(24) on O74, Q is confined to X={01,10}. On Y, the two D
copies see {13,31,32}, while P sees {02,32}. The same allocation
proves the final rule.

## 4. The two helpers always work on one of the two targets

There are fourteen adjacent classes avoiding12. The following
small cut table records which hole groups each class meets in the
four rules. A dash means that it misses every eligible hole position.
For example, XY means the source has at least one corner in each
of X,Y. The entries follow by intersecting the directed cut C(S)
with the explicitly listed hole sets.

| Source side S | A=23, T=O63 | A=23, T=O71 | A=24, T=O63 | A=24, T=O74 |
|---|---|---|---|---|
| 234 | Z | X | X | Y |
| 02 | XY | Y | XY | X |
| 03 | XY | Y | Y | XY |
| 124 | XZ | Z | — | XY |
| 04 | X | XY | XY | XY |
| 123 | — | XZ | XY | X |
| 12 | X | XZ | Y | XY |
| 034 | X | XY | Y | XY |
| 024 | X | XY | X | X |
| 023 | Y | Y | Y | XY |
| 23 | — | — | XY | Y |
| 24 | XZ | X | — | — |
| 34 | XZ | X | XY | Y |
| 012 | XY | X | XY | Y |

### A=C(23)

The helpers have different classes, neither C(23). The O63 rule
fails only if one helper is C(123), or both helpers belong to

    {C(04), C(12), C(034), C(024)}.

The singleton Y-only and Z-only classes cannot cause a failure,
because each occurs in just one class and the helpers are distinct.

On O71, C(123) meets two groups and every other available helper
is nonempty, so the first exception is solved. Every class in the
displayed four-class family meets two O71 groups, so the second
exception is solved as well.

### A=C(24)

The O63 rule fails only if a helper is C(124), if the two helpers
are C(234),C(024), or if both helpers lie in

    {C(03), C(12), C(034), C(023)}.

On O74, C(124) meets both groups and every available helper is
nonempty. The pair C(234),C(024) meets opposite groups. Each
class in the displayed four-class family meets both groups.
Thus every exception is solved on O74.

This completes both repeated-class possibilities, and hence the
entire zero-edge common-target orbit with D's intersection an
opposite pair of edges.

## Scope

Only the fixed three-variety geometric normal form is used. The
fourteen-row table lists the cuts avoiding one directed corner,
not inventories or repeated-colour refinements. The theorem follows
from the displayed four-source edge matchings and four explicit
two-hole completion rules.
