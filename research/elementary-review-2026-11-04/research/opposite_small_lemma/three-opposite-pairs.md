# Three opposite pairs and two arbitrary sources

**Proved elementary lemma.** Two copies of each of any three distinct
opposite-repeat varieties, together with any two further five-colour
cubes, admit an opposite-repeat corner assembly.

There is no multiplicity restriction on the two additional cubes.
This is stronger than the corresponding special case of the earlier
finite eight-cube lemma. It does not settle all its six-opposite cases.

## 1. Undirected notation and a robust-six observation

Identify an opposite variety with its undirected four-cycle on the five
colours. Each edge denotes both directed corner types. Any two distinct
four-cycles on five vertices share one or two edges.

For a fixed four-cycle T and any two-edge subset F of T, exactly one
other four-cycle has intersection F with T. If the two edges of F
are adjacent, its remaining vertex must be the fifth colour. If the
two edges are disjoint, the alternative way to complete them on the
same four vertices is unique.

Suppose three distinct opposite varieties A,B,C each share at least
two edges with a target T, and their intersections together cover all
four edges of T. Then two copies of each A,B,C can fill **any six**
of T's eight corners. Indeed, a set of corners on one target edge has
at least two neighbouring sources. A set meeting two target edges has
at least four neighbours: at most one of A,B,C can have its intersection
with T confined to the complementary two edges. A set meeting three
or four target edges sees all six sources. These are Hall's inequalities
for every set of at most six corner positions.

The two arbitrary additional sources each have at least two corners in
common with T, so they can be assigned two distinct positions. The six
opposite sources fill the remaining positions.

## 2. When a robust-six target exists

If one of A,B,C shares two edges with each of the other two, use it as T.
The preceding observation applies.

If exactly one pair, say A,B, shares two edges, take T=A symmetric-difference B.
This is again a four-cycle: if the common edges are adjacent, the two
alternative fourth vertices form the new cycle; if they are disjoint,
the alternative edge pairs form it. Its intersections with A and B
are complementary two-edge subsets, so already cover T. Since C
shares one edge with each A and B,

    |C∩T| = |C∩A| + |C∩B| − 2|C∩A∩B|.

The right side is either zero or two. It cannot be zero because two
four-cycles on five vertices always share an edge. Thus C also shares
two edges with T, and the robust-six observation applies.

It remains that A,B,C are pairwise one-edge-intersecting. Normalize two
of them to

    X={13,14,23,24},   Y={01,04,13,34}.

The third cannot have the omitted colour of X or Y, because two distinct
four-cycles on the same four vertices share two edges. Listing the
three cycles on each of the other four-vertex sets leaves only

    {02,03,24,34}, {02,04,12,14},
    {02,03,12,13}, {01,03,12,23}.

For the third choice all three cycles share the edge13. The target
{12,13,24,34} meets them in the three two-edge sets
{13,24}, {13,34}, {12,13}; these cover all four target edges, so
the robust-six observation applies again.

In each of the other three choices, the three pairwise intersection
edges form a path on four colours. All such triples are equivalent
under colour relabelling. To see uniqueness, the cycle containing
the two outside path edges is determined by avoiding the middle edge;
each other cycle consists of its two adjacent path edges completed
through the fifth vertex. We may therefore use the normal form

    X={13,14,23,24} [O60],
    Y={02,04,23,34} [O64],
    Z={01,03,14,34} [O68].

## 3. The remaining normal form

For the doubled sources 2X+2Y+2Z, the following four targets have the
stated useful property: the six sources fill every set of six target
corners obtained by leaving any two distinct corners in H unused.
Here an undirected edge in H again denotes both directions.

| Target T | Forced edge filled by two core copies | H | Opposite varieties avoiding H |
|---|---|---|---|
| {03,04,23,24} [O63] | 03, by Z | {04,23,24} | Z,V |
| {02,03,24,34} [O65] | 24, by X | {02,03,34} | X,W |
| {03,04,13,14} [O66] | 04, by Y | {03,13,14} | Y,W |
| {01,04,13,34} [O67] | 13, by X | {01,04,34} | X,V |

where

    V={02,03,12,13} [O72],
    W={01,04,12,24} [O70].

The six-corner completion property is immediate in every row. The
indicated two core copies fill both directions of the forced edge.
The other four copies form two two-copy pools on H. Each pool fits
two of H's three edge pairs, and their intersection is one edge pair.
Thus the first pool's exclusive pair requires at most two copies,
the second pool's exclusive pair requires at most two, and all four
copies together fill any four of H's six corner positions.

Each H is a three-edge path on four vertices. An adjacent cut meets
H because a two-three cut cannot place all four path vertices on one
side. Its intersection contains one directed corner for every crossed
path edge. An opposite variety meets H in both directions of any
shared edge. The last column follows by considering the omitted vertex:
a four-cycle avoiding a three-edge path must omit an internal path
vertex, and either internal vertex determines exactly one such cycle.

### Two adjacent additional sources

The first two paths H are complementary edge sets in the complete graph
on {0,2,3,4}. A two-three cut splits these four vertices nontrivially,
and therefore crosses three or four of that complete graph's edges.
It consequently meets at least one of these two paths in at least two
corners. The other adjacent source meets that path in at least one
corner. Assign the sources to two distinct corners of H and complete
with the six opposite copies.

### One adjacent and one opposite additional source

The two sets {Z,V} and {X,W} in the first two rows are disjoint.
Thus the additional opposite source meets H in at least one of these
rows, giving it at least two directed corners there. The adjacent
source has at least one corner there. Again distinct holes can be
assigned and the core completes the assembly.

### Two opposite additional sources

If both meet H in any row, each has at least two directed corners in H,
and the same construction works. Failure of the first two rows would
therefore require one extra source from {Z,V} and the other from {X,W}.
The third row eliminates Z+X and V+X; the fourth eliminates Z+W.
Only V+W remains.

For V+W use the target {12,14,23,34} [O61]. The two extra sources fill
12 and21. The six core sources fill the six directed corners on
{14,23,34}: X fits the first two edge pairs, Y the last two, and Z
the first and last. Hall's inequalities hold because each edge pair
has four neighbours, any two edge pairs see all six sources, and
all six positions see all six. This completes the last case.

## Consequence

A failing pool of size at least eight cannot contain three distinct
opposite varieties twice each. In particular, in the remaining diffuse
fourteen-cube branch, at most two opposite varieties can occur twice.
An elementary treatment of six-opposite cores with multiplicity profiles
(2,2,1,1), (2,1,1,1,1), or(1,1,1,1,1,1) is still needed for the full
eight-cube lemma.

