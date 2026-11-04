# Independent audit of the common-missing-pair lemma

4 November 2026

**Result: `../root/eight-plus-three-common-missing-pair.md` passes
independent mathematical audit.** No inventory tests were used.

## Projection calculation

For an adjacent cut with x outset colours among the two poles and
y among the three ring colours, the intersections with the two
oriented pole/ring cuts have sizes x(3−y) and y(2−x). The possibilities
for x+y=2 or3 give the two family pairs(6,0),(0,6) and exactly the
four nonfamily pairs(4,0),(2,1),(1,2),(0,4). A nonfamily opposite
cycle crosses the pole/ring partition on exactly two edges, so
its pair is(2,2); a family cycle gives(4,4). The three displayed
projection implications follow, including the family varieties.

## The initial array bounds

Let a be the maximal opposite-variety count and b,c the other two,
so O=a+b+c and a≥b,c. For the target of count a, the opposite-source
contributions in the two rows are a+b and a+c. Both are at least
O/2, because the omitted count is at most its maximal companion.

Consequently each cell has at least O/2+min(P₀,Q₀) neighbours. The
assumption O+min(P₀,Q₀)≥4 implies this is at least two. Each row
misses just the b or c sources of the other row, and therefore has
at least8−O/2≥4 neighbours. Each column has all O opposite sources
and its own-sign adjacent sources, at least four in total. Diagonal
pairs and all unions of three or four cells neighbour every chosen
source. Partial cells introduce no new inequality because their
positions have identical source neighbourhoods. Hall therefore
matches the eight target positions.

## Hall deficiency and retargeting

The second branch has P₀≥5, so a positive variety has two universal
copies for its own target. A deficient set has size at least three
and contains a tricoloured position. All P₀ chosen positive sources
are consequently neighbours. With E the other neighbours and U the
unselected positive corners, integrality gives

    |E|+u≤κ−1≤2.

Every survivor has p≤u. Chosen family opposite sources cannot
survive, since p=4. Thus at leastκ−|E|≥u+1 chosen negative-family
sources remain, and the whole surviving pool has at least4+u
sources. Additional positive-family sources are counted in E;
additional negative-family sources are included in j. This keeps
the physical-source bookkeeping correct in all cases.

For j=3 and j=2, the displayed projection bounds provide respectively
one and two negative corners per required other survivor, and the
listed assignments to one half follow directly.

For j=1, u=0 and at least three other sources survive, each with at
least four of the six negative corners. Two of the three row-pairs
contain at least three corners of one chosen survivor W. Any other
survivor has at least two corners in that four-position half, by
the intersection bound4+4−6=2. W and two other survivors satisfy
source-side Hall: singletons have at least two positions, pairs at
least two, and the triple at least three because W itself has three.
The one universal negative source fills the remaining position.

Finally four removed chosen positive sources fill the other target
half. They are distinct from the survivors, and P₀≥5 guarantees
availability. The target is in the original missing-pair family.

The proof is self-contained relative to the basic corner model and
Hall's theorem. It uses neither the fifteen-cube threshold nor any
fourteen-cube failure classification. No mathematical correction is
needed.
