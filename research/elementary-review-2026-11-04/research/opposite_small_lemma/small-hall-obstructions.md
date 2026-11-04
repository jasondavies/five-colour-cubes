# Opposite-target Hall obstructions in fourteen-source diffuse pools

**Elementary observation.** Suppose a fourteen-source pool has at
most two copies of any opposite variety and at most four copies of
any adjacent tricolour class. A Hall obstruction for an opposite
target has at most five positions.

Every source has at least two compatible target corners, so any set
of seven or eight target positions meets every source.

For six positions, inspect the omitted pair. If the two omitted
corners are the two directions of one undirected edge, only opposite
sources can be confined to them. There are exactly two such opposite
varieties, allowing at most four sources; the six-position set
therefore meets at least ten sources. If the omitted corners belong
to different undirected edges, no opposite source is confined to them.
At most two adjacent classes have exactly this two-corner target
intersection, allowing at most eight sources. The six-position set
therefore meets at least six sources.

This proves the observation.

## A sufficient degree condition

Under the same hypotheses, an opposite target assembles whenever
each of its eight corners belongs to at least four source copies.

Position sets of size at most four satisfy Hall immediately. If a
five-position set had at most four source neighbours, each of its
corners having degree at least four would force all four neighbours
to contain all five positions. An adjacent cut contains at most four
corners of an opposite target, and a different opposite variety also
contains at most four. Thus all four neighbours would have to be
copies of the target variety, contradicting the cap of two. Larger
sets satisfy Hall by the preceding observation.

This sufficient condition is not guaranteed in all diffuse pools.
For example, take one source in each adjacent class
\(1,8,10,13,14,17\), and opposite sources

\[
2O60+O66+2O67+O68+O70+O71.
\]

Every class has multiplicity at most one, every opposite variety at
most two, and the total is fourteen. The undirected edges with at
least one direction of degree less than four are
\(02,03,12,23,34\). Their complement is a five-edge graph containing
no four-cycle, so no opposite target meets the degree-four criterion.
The pool nevertheless assembles by the established small-core lemmas.
