# Eliminating the repeated-colour labels exactly

This is a proved reduction, not an empirical pattern.

Fix the twenty adjacent tricolour-class counts g_j and the fifteen
opposite-variety counts o_i. Write P_j for the two poles of adjacent class
j. Its three physical varieties are indexed by the repeated colour
r outside P_j. Its tricoloured corners depend only on j.

## The conflict graph

For classes j,k with available copies, reserve one source from each
(two copies when j=k). Put an edge j--k if there is a directed cut C
whose six corners can be matched by the remaining coarse pool and whose
pole pair {p,q} satisfies p in P_j, q in P_k, p!=q, after possibly
interchanging p and q. A diagonal edge is recorded as a loop.

The definition uses only coarse counts and six-corner matching; it never
uses a repeated-colour label. In particular, if the two reserved cubes
both repeat r, then r is outside P_j union P_k and hence outside {p,q}.
They provide the target's two bichromatic corners (r,r,p),(r,r,q), and
the other six cubes provide its tricoloured corners.

Conversely, every adjacent-target assembly contains exactly two cubes
used at bichromatic corners. They must be adjacent-repeat cubes with
the target's repeated colour. Reserving them witnesses the corresponding
edge of this graph. Therefore:

**Exact criterion.** A physical refinement has no adjacent-target
assembly if and only if no two cubes with the same repeated colour
occupy conflicting classes (and a looped class has at most one cube
of each repeated colour).

One first checks the fifteen opposite targets. Their feasibility is
already determined by the coarse counts.

## A list-multicolouring problem on at most twenty vertices

Each active class j has the three allowed colours V minus P_j.

* A looped class must use g_j distinct allowed colours.
* A loopless class may be assumed monochromatic when deciding whether
  any failing refinement exists.

The second assertion is exact: start with a failing refinement and merge
all copies of a loopless class into any one repeated colour already used
there. No new colour is introduced at that vertex, and no within-class
conflict is created because there is no loop. Thus this operation
preserves failure.

Consequently the existence of a failing refinement is equivalent to
choosing disjoint colour subsets on adjacent graph vertices, with demand
g_j at a looped vertex and demand one at a loopless vertex, from the lists
V minus P_j. This removes the need to enumerate the compositions of g_j
among three physical varieties.

## Two elementary infeasibility certificates

1. If S is a clique of active classes, define d_j=g_j for a looped class
   and d_j=1 otherwise. Then a failing refinement requires

       sum_{j in S} d_j + |intersection_{j in S} P_j| <= 5.

   The required repeated-colour sets are pairwise disjoint and all avoid
   every common pole colour. This is just the pigeonhole principle.

2. If two looped classes have count three and disjoint pole pairs, they
   use their entire three-element lists. A common graph neighbour would
   have to repeat a colour belonging to both disjoint pole pairs. Hence
   a failing refinement has no such common neighbour.

The implementation in `conflict_graph.py` returns graph edges together
with six-corner target witnesses. It also implements the exact list
problem; `clique_obstruction` returns the first certificate of kind1.

## Concrete improvement over arbitrary-reservation robustness

The coarse all-adjacent inventory

    g0=3, g9=1, g10=3, g15=2, g17=2, g19=3

has fourteen cubes. Its only robust six-corner cuts are classes0 and17,
with disjoint pole pairs01 and24. All opposite targets fail; the source
union supports opposite targets60 and68. Repeated colours can be chosen
to make both robust cuts' bichromatic demands unavailable, so the robust
test alone cannot settle the pool.

The full conflict graph has looped class0 and a triangle on0,9,10.
These classes have common pole1 and demand3+1+1. The clique inequality
would require3+1+1+1<=5, a contradiction. Thus EVERY refinement solves.

For example, the physical counts

    x0=x1=x2=x27=x52=x53=1, x30=x59=3, x47=2

pass the weak robust test but build adjacent target30. This is why a
proof based only on robust cut pole pairs loses essential information.

## O3 cover checks (finite evidence, not the hand proof)

With the known caps g_j<=5, each opposite count<=3, shared-four pair
counts<=7, and missing-pair counts<=7, the Hall cover test at3O60 gives:

| Cover mask | Coarse vectors left after opposite targets | Failing refinements |
| --- | ---: | ---: |
|15|318|8, all with adjacent profile5,3,3|
|23|0|0|
|27|16|0|
|30|82|0|
|51|149|0|
|53|0|0|
|54|13|0|
|58|338|0|
|102|0|0|

Every rejected vector has a certificate of kind1 except four symmetric
vectors in cover58, which have certificates of kind2. These data guide
the short hand arguments. They are not substituted for a proof that the
cover reduction is complete or for symbolic derivations of the count
cases. The separate note `o3-mask54-hand-proof.md` supplies such a fully
elementary derivation for cover54.
