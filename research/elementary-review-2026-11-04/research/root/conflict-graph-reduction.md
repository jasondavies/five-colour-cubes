# Exact reduction of repeated-colour choices to a small graph

Fix the twenty adjacent-class counts g_j and the fifteen opposite counts.
First test whether an opposite target can be assembled. That question
depends only on these thirty-five counts because opposite targets have
only tricoloured corners.

For adjacent class j let P_j be its pole pair. Its allowed repeated
colours are L_j=V\P_j, a list of three colours. Construct a graph on
the nonempty adjacent classes, allowing loops, as follows.

Reserve one source copy from each of classes j,k (two copies if j=k).
Join j and k if there is an oriented target cut T such that:

1. Its two poles can be assigned to the two reserved pole pairs, one
   pole lying in P_j and the other in P_k.
2. Its six tricoloured corners can be matched using the remaining
   sources, with their fixed coarse multiplicities.

The graph is independent of the repeated-colour refinement. If the two
reserved cubes both repeat r, then r lies outside P_j and P_k, and
therefore outside the target poles. They supply the target's two
bicoloured corners. The six-corner matching completes an assembly.

Conversely, every assembly of an adjacent target reserves exactly two
cubes for its two bicoloured corners. These cubes repeat the same
colour, and the other six cubes witness precisely the graph edge just
defined. Thus this construction is exact, not merely a sufficient test.

## Characterization

Assume all opposite targets fail. A repeated-colour refinement fails
if and only if:

* Classes joined by an edge use disjoint sets of repeated colours.
* In a class with a loop, each repeated colour occurs at most once.

Equivalently, a looped vertex j needs g_j distinct colours from its
three-element list L_j. A loopless vertex needs at least one colour
from that list. For deciding whether any failing refinement exists,
one may take every loopless class monochromatic: collapsing its
repeat set to one colour already used cannot create a conflict.

This last simplification concerns existence, not enumeration of all
refinements. For example, the opposite-four family still has91 actual
refinements, many of which are not monochromatic.

## Elementary pigeonhole certificates

For a pairwise-adjacent set S of class vertices define

    d_j = g_j if j has a loop, and d_j=1 otherwise.

All these demanded colours must be different, and they must lie in
the union of the lists. Therefore any failure satisfies

    Σ_(j∈S) d_j ≤ |union_(j∈S) L_j|
                 = 5−|intersection_(j∈S) P_j|.

A violation is an elementary certificate of solvability.

There is also a useful list-specific obstruction. A looped class of
size three uses all colours outside its poles. Any neighbour must
therefore repeat a colour inside those poles. Two looped size-three
classes with disjoint pole pairs cannot have a common nonempty
neighbour, because that neighbour would need a repeated colour in
both disjoint pairs.

Many of the remaining three-opposite Hall-cover cases reduce to one
of these two pigeonhole arguments. The implementation is
`../robust_route/conflict_graph.py`, which uses only exact augmenting
path matching and a small list-colouring backtrack. This reduction
does not by itself establish the global W=36 identity or N₅=15.

