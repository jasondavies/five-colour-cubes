# One doubled opposite in the endpoint type of zero-edge triad

**Theorem.** Let

    D=O71={01,02,14,24},
    P=O61={12,14,23,34},
    Q=O63={03,04,23,24}.

Two D sources, one P, one Q, and ten adjacent sources with class
multiplicities at most three assemble an opposite target.

The three varieties are pairwise nonneighbouring and their union is
K5 minus edge13. Their common high target O60={13,14,23,24} has
opposite frequency zero on13. The doubled variety omits endpoint3
of that zero edge. This note treats this geometric type directly;
it does not assume any orientation of13 is absent from the adjacent
sources.

## 1. Most repeated adjacent classes already solve

If four opposite sources match the four corners of a high rectangle
of an adjacent class A, then four hypothetical A sources fill the
forward half of that target and the opposite sources fill the
reverse half. Two actual A sources and any two actual adjacent
helpers can replace the four hypothetical sources. Choose distinct
underlying edges met by the two helpers and, when necessary, swap
the two corner directions on the chosen edge with its opposite
source. The swaps preserve the opposite-source compatibilities.

Thus a failing pool can have a repeated class A only when these four
opposite sources fail every high rectangle of A.

For a positive cut A=C(uv), the following table exhibits a matching
whenever its pole pair is not03 or34. Reverse all directions to cover
the negative cut with the same pole pair.

| Pole pair uv | Rectangle columns | 2D positions | P position | Q position |
|---|---|---|---|---|
| 01 | 24 | 14,02 | 12 | 04 |
| 02 | 14 | 24,01 | 21 | 04 |
| 04 | 12 | 02,01 | 41 | 42 |
| 12 | 04 | 20,10 | 14 | 24 |
| 13 | 04 | 14,10 | 34 | 30 |
| 14 | 02 | 42,10 | 12 | 40 |
| 23 | 04 | 24,20 | 34 | 30 |
| 24 | 01 | 41,20 | 21 | 40 |

The only possibly repeated adjacent classes in a failure are therefore

    C(03), C(124), C(34), C(012).                  (B)

Each other class has multiplicity at most one. If no class repeats,
the nine-distinct-class theorem gives an assembly. Otherwise choose
a repeated class from(B). By reversing all corner directions, it is
enough to consider A=C(03) or A=C(34).

## 2. A repeated C(03)

Use target D. The two A corners are X={01,02}. Assign two actual A
copies there. The P source sees exactly the two directions of14 on
target D; Q sees exactly the two directions of24. The two D sources
are universal.

Two additional adjacent helpers complete an assembly whenever they
can occupy different corners outside X and their pair is neither
{14,41} nor{24,42}. Under this condition at least one corner remains
for each of P,Q; assign them those corners, and let the two D sources
fill the other two remaining positions.

At most one of the eight remaining adjacent sources has no corner
outside X: the only class whose D-intersection lies in X is A, and
at most one A copy remains after reserving two. Thus at least seven
helpers have nonempty residual intersections.

If a helper has two or more residual corners, these lie on different
underlying edges. With any other nonempty helper, choose a corner on
each of two different edges. That pair completes the assembly.
If all residual intersections are singletons, two lying on different
edges likewise complete it. Consequently failure forces every helper
corner outside X onto one underlying target edge e.

All ten adjacent classes then have their D-intersections inside
X together with both directions of e. The possibilities are:

| Edge e | Eligible adjacent classes | Maximum source count under(B) |
|---|---|---:|
| 01 or02 | C(03) | 3 |
| 14 | C(03),C(01),C(024),C(013) | 6 |
| 24 | C(03),C(02),C(023),C(014) | 6 |

These are obtained by intersecting directed cuts with the four-cycle
D. In the last two rows only C(03) belongs to(B); the other three
classes occur at most once. Every bound is less than ten. Hence the
required helper pair exists, and this case assembles.

## 3. A repeated C(34)

Again use target D. Put the two A sources at41,42, P at14, and Q at24.
Two adjacent helpers at different corners of

    E={01,10,02,20}

would let the two D sources complete the target.

If such a two-corner helper matching does not exist, the bipartite
matching cover of size at most one has one of two forms.

First, at most one source meets E. Then at least nine adjacent sources
avoid both underlying edges01,02. Only C(34) and C(012) do so: the
three vertices0,1,2 must stay on one side of the cut. Their total
capacity is six, a contradiction.

Second, all adjacent E-corners lie in one specified corner. The four
possibilities give:

| Sole allowed corner | Eligible classes besides C(34),C(012) |
|---|---|
| 01 | C(02),C(024),C(023) |
| 02 | C(01),C(014),C(013) |
| 10 | C(134),C(13),C(14) |
| 20 | C(234),C(23),C(24) |

Every extra class in this table lies outside(B), so occurs at most
once. Each row therefore accommodates at most3+3+1+1+1=9 adjacent
sources, again contradicting the total of ten.

The matching exists and gives an assembly. This treats both remaining
types of repeated adjacent class and proves the theorem.

## Scope

The only tables classify ten pole pairs and directed cuts against
specified two- or three-edge conditions. They provide explicit
matchings or direct capacity bounds. No exhaustive inventory
classification is used.

The other zero-edge triad type, in which the doubled variety contains
both endpoints of the globally missing edge, is handled separately.
