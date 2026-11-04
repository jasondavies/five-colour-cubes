# Five opposite cubes, one doubled variety, and a triple adjacent class

**Status: elementary proof.** This note continues the grid argument in
`six-opposites-three-adjacent.md`.

**Lemma.** A fourteen-source pool is soluble if it has exactly five
opposite sources, at most one opposite variety is repeated, every
opposite variety occurs at most twice, and one adjacent tricolour
class has at least three copies. Here we may assume that every adjacent
class has at most three copies, since the four-class case is already
settled separately.

Only opposite targets are used. The opposite inventory has profile
\(1^5\) or \(2,1,1,1\).

## 1. The grid cover

Let the triple adjacent class be \(A=C(01)\), with its two-by-three
grid of directed corners. If the five opposite sources match all four
positions of a two-column rectangle, use those four sources on the
reverse rectangle and the remaining opposite source plus three \(A\)
on the forward rectangle. We may therefore suppose every rectangle
has rank at most three.

As in the six-opposite proof, the grid has rank at most four. Hall's
theorem gives a cover \(H\) with

\[
|H|+\#\{\text{opposite sources with pattern not contained in }H\}\le4.
\]

A cover of size at most two is impossible. A four-position rectangle
is also impossible: five capped opposite sources supported on it match
its four corners. An absent corner would confine five sources to three
positions, containing only two varieties and hence at most four copies;
the other Hall inequalities are stronger still.

There are thus two cases.

* All five source patterns lie in four positions with column sizes
  \(2,1,1\).
* Four source patterns lie in three positions, and the remaining
  source lies outside them.

In the second case the three positions occupy three distinct columns.
Otherwise they support only two varieties, which can provide at most
three sources when only one variety may be doubled. The three-position
case must therefore consist of \(2P,Q,R\), where \(P,Q,R\) are the
three varieties given by its two-position subsets, and one further
variety \(S\). The varieties \(P,Q,R\) form a line: their pairwise
intersections have two undirected edges, their union has six, and every
union edge belongs to two of the three cycles.

## 2. Selecting a target

In the four-position case, select the central target \(T\) joining
the two singleton-column positions, as in the preceding note. Every
source meets \(T\) in at least two undirected edges. Each target edge
is absent from only two of the five possible source varieties. Since
at most one variety is doubled, those two varieties account for at
most three of the five sources. Thus every target edge has at least
two source copies.

If a variety \(D\ne T\) is doubled, the two \(A\)-compatible corners
of \(T\) include one outside \(D\cap T\). This follows directly
from the two central-target diagrams in the preceding note: each of
the four noncentral varieties contains exactly one of the two
singleton-column corners.

In the three-position case, select the high target \(T\) of \(S\)
in the line \(P,Q,R\). An opposite variety outside a line intersects
its three targets in \(2,1,1\) undirected edges, so this target exists.
All five sources then meet \(T\) in at least two undirected edges.
The copies of the line varieties themselves supply every target edge
at least twice: if \(T=P\), its two copies suffice; otherwise its own
copy and a copy of one of the other line varieties cover each edge.

If \(T\ne P\), the two \(A\)-compatible target corners lie in the
two distinct pairwise-intersection blocks of the line. In particular
one is outside \(P\cap T\). If \(T=P\), the doubled source is
universal and creates no exception.

Thus, in both cases, we have a target \(T\) with these properties:

1. each of the five opposite sources sees at least two target edges;
2. each target edge is seen by at least two sources;
3. the target has exactly two corners in \(A\), denoted \(a,b\);
4. if the doubled variety \(D\) is not \(T\), at least one of
   \(a,b\) lies outside \(D\cap T\).

## 3. Five-source completion after the two A corners are reserved

Reserve \(a,b\) for two \(A\) copies. The five opposite sources can
fill **any five of the remaining six positions**.

To prove this by Hall, a position set using one target edge has at
least two source neighbours. A set using at least three target edges
sees all five sources. A set using two target edges has at least four
source neighbours, except possibly when the sole variety avoiding
those two edges is the doubled variety \(D\). In that case it has
three neighbours, but the two edges are precisely the complement of
\(D\cap T\), and one of their four corners has already been reserved
as \(a\) or \(b\). At most three of their positions remain. Every
Hall inequality therefore holds for every set of at most five
unreserved positions.

Here we used the elementary uniqueness fact that, for a fixed target
and a fixed two-edge subset, exactly one other opposite variety has
that subset as its complete intersection with the target. It follows
by closing a two-edge path through the fifth colour, or by choosing
the other four-cycle containing a pair of opposite edges.

## 4. An additional adjacent source exists

There are nine adjacent sources in the pool. At most two adjacent
tricolour classes have target intersection contained in \(\{a,b\}\).
Indeed every adjacent source meets an opposite target in at least two
corners on distinct underlying edges, so such an intersection must
equal \(\{a,b\}\). A two-corner pattern on a target four-cycle is
either a directed two-edge star, which determines one adjacent class,
or consists of two opposite edges, which determines at most two classes
according to the placement of the fifth colour.

Each class has at most three copies. Those classes account for at
most six of the nine adjacent sources. Some other adjacent source
therefore has a target corner \(c\notin\{a,b\}\). Use it at \(c\),
the two \(A\) copies at \(a,b\), and the five opposite sources on
the remaining five positions. This proves the lemma.

## Remaining five-opposite profile

The argument leaves only opposite inventory \(2,2,1\). A separate
line-hole construction handles the case in which the two doubled
varieties share four directed corners. The remaining case with two doubled opposite varieties sharing only
two directed corners is proved separately in
`five-opposites-nonneighbouring-pairs.md`.
