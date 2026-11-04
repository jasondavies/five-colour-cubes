# Five opposite sources with two nonneighbouring pairs

**Status: elementary proof.** This closes the last five-opposite case
with a triple adjacent class. The proof has one overlapping grid
configuration and three disjoint grid configurations. The small table
below gives explicit corner allocations, rather than an enumeration
of inventories.

**Lemma.** A fourteen-source pool with exactly five opposite sources,
no opposite variety occurring more than twice, and an adjacent class
of multiplicity at least three is soluble.

We may assume every adjacent class has at most three copies, using the
separately established four-class lemma. The preceding two notes settle
the cases with at most one doubled opposite variety, and with two
doubled varieties sharing four corners. It remains to handle

\[
2P+2Q+C,
\]

where \(P,Q\) share only one undirected edge and \(C\ne P,Q\).
There are nine adjacent sources in the pool, each class occurring at
most three times. Normalize a triple class to \(A=C(01)\).

## 1. Two possible grid shapes

If the opposite sources match all four corners of a two-column
rectangle of the \(A\) grid, four opposite sources fill its reverse,
and the fifth opposite source plus three \(A\) fill its forward
corners. Otherwise the three rectangle ranks are at most three.
As before, the full grid has rank at most four, and Hall gives a cover
\(H\) of size three or four, with at most one source outside a
three-position cover and none outside a four-position cover.

Both doubled source patterns must lie in \(H\): putting one of them
outside would put two source copies outside. Neither doubled pattern
is a whole rectangle. Such a rectangle would force \(H\) to be that
rectangle; five capped opposite sources on it match all four positions.
Thus the two patterns each contain two grid positions.

If they share a position, their union has three positions. These cannot
occupy all three columns: the three two-position patterns on one
position per column form a line of pairwise neighbouring varieties.
Since \(P,Q\) are nonneighbouring, the union has column sizes \(2,1\).

If the patterns are disjoint, their four positions cannot form a
two-column rectangle for the same matching reason. Their column sizes
are \(2,1,1\), and \(C\)'s pattern must also lie in those four
positions. These are the only two shapes.

## 2. Overlapping patterns

Normalize the patterns to

\[
P\cap A=\{02,03\},\qquad Q\cap A=\{12,03\}.
\]

The opposite varieties are

\[
P=O65=\{02,03,24,34\},\qquad
Q=O73=\{01,03,12,23\},
\]

where undirected edges denote both corner orientations.

If \(C\) contains edge \(13\), its corner \(13\), one \(P\)
corner \(02\), one \(Q\) corner \(12\), and another \(P\) or
\(Q\) corner \(03\) match the rectangle on columns 2 and 3. We
are done.

Otherwise \(C\) contains edge \(04\) or \(14\). Indeed the
three forbidden edges \(13,14,04\) form a four-vertex path. Exactly
two four-cycles on five vertices avoid that path: they omit one or
the other internal vertex and are precisely \(P,Q\). Omitting an
endpoint leaves a vertex of degree one in the available four-vertex
graph, and omitting the fifth vertex leaves only three available
edges. Since \(C\ne P,Q\), it must meet the path.

If \(C\) contains \(04\), use target
\(T=O63=\{03,04,23,24\}\). Assign two \(A\) copies to \(03,04\)
and \(C\) to \(40\). The five remaining positions are

\[
E=\{23,32,24,42,30\}.
\]

The two \(P\) copies see \(30,24,42\), and the two \(Q\) copies
see \(30,23,32\). They can fill any four of these five positions:
the two three-position sets share one position, and each has two
private positions. Any adjacent source meeting \(E\) supplies the
remaining corner.

Only the class \(A\) avoids \(E\). Avoiding both directions of
\(23\) and \(24\) puts colours \(2,3,4\) on one side of the cut
and \(0,1\) on the other. Avoiding \(30\) determines the orientation
to be \(A\). Since there are nine adjacent sources and only three
can belong to \(A\), a source meeting \(E\) exists.

If \(C\) instead contains \(14\), use
\(T=O68=\{01,03,14,34\}\). Put two \(A\) copies at \(03,14\)
and \(C\) at \(41\). The five remaining positions are

\[
E=\{01,10,30,34,43\}.
\]

The two \(P\) copies see \(30,34,43\), and the two \(Q\) copies
see \(30,01,10\), so again they fill any four. A class avoiding
\(E\) must keep \(0,1\) together, keep \(3,4\) together, and
orient the former pair toward the latter. Colour 2 can join either
side. Thus at most two classes avoid \(E\); their combined
multiplicity is at most six, and one of the nine adjacent sources
meets \(E\). This closes the overlapping case.

## 3. Disjoint patterns: two explicit ways to complete

There are three configurations up to exchange of the rows and
permutation of the columns. The table lists all of them. Each source
variety is determined by its two grid positions, so the three possible
values of \(C\) are the remaining two-position patterns in the four
positions.

| Doubled varieties \(P,Q\) | Grid patterns \(P\cap A;Q\cap A\) | Central target \(T\) | Common edge \(d=P\cap Q\) | Edge \(e\) absent from \(P,Q\) | Possible \(C\) |
|---|---|---|---|---|---|
| \(65,70\) | \(02,03;12,04\) | \(63=\{03,04,23,24\}\) | \(24\) | \(23\) | \(63,64,73\) |
| \(61,65\) | \(12,14;02,03\) | \(68=\{01,03,14,34\}\) | \(34\) | \(01\) | \(68,71,73\) |
| \(71,73\) | \(02,14;12,03\) | \(68=\{01,03,14,34\}\) | \(01\) | \(34\) | \(61,65,68\) |

In each row, let \(a\) be the \(A\)-corner of \(P\) that belongs
to \(T\), and let \(b\) be the corresponding \(Q\) corner. The
target \(T\) consists of the four undirected edges underlying
\(a,b,d,e\). Every permitted \(C\) contains \(e\) and at least
one of the edges underlying \(a,b\).

**First completion.** If any adjacent source has a corner on edge
\(e\), assign it there and \(C\) to the reverse corner of \(e\).
Assign two \(A\) copies to \(a,b\). The remaining four positions
are the reverse corners of \(a,b\) and the two directions of \(d\).
The two \(P\) copies fill the reverse of \(a\) and one direction
of \(d\); the two \(Q\) copies fill the reverse of \(b\) and the
other direction of \(d\).

**Second completion.** Suppose \(C\) contains the edge underlying
\(a\). Use target \(P\). Assign the two \(Q\) copies to both
directions of \(d\), assign \(C\) to the reverse of \(a\), and
assign two \(A\) copies to the two corners in \(P\cap A\). Three
target positions remain. Any adjacent source meeting one of them
fills that position; the two universal \(P\) copies fill the other
two. When \(C\) contains the edge underlying \(b\), the symmetric
construction uses target \(Q\).

Here are the three-position sets supplied by the second completion:

| \(P,Q\) | If \(C\) contains the private P edge: target \(P\), remaining set | If \(C\) contains the private Q edge: target \(Q\), remaining set |
|---|---|---|
| \(65,70\) | Edge \(03\): \(\{20,34,43\}\) | Edge \(04\): \(\{01,10,21\}\) |
| \(61,65\) | Edge \(14\): \(\{21,23,32\}\) | Edge \(03\): \(\{20,24,42\}\) |
| \(71,73\) | Edge \(14\): \(\{20,24,42\}\) | Edge \(03\): \(\{21,23,32\}\) |

Fix either applicable second completion, and let \(E\) be the union
of its three-position set with both directions of \(e\). An adjacent
source meeting \(E\) enables one of the two completions. In every
entry of the table, \(E\) consists of two bidirected edges and one
further directed edge joining their components.

If the two bidirected edges are adjacent, avoiding them puts their
three vertices on the same side of the cut. The remaining two
vertices must occupy the other side, and the further directed edge
fixes the orientation. There is at most one avoiding class. If the
two bidirected edges are disjoint, each pair must stay together on
opposite sides. The further directed edge fixes their orientation,
and the fifth colour has two choices of side. There are at most two
avoiding classes.

In either case those classes account for at most six adjacent sources.
There are nine. An adjacent source meeting \(E\) therefore exists,
and the pool assembles. This proves the lemma.

## Combined consequence

Together with `six-opposites-three-adjacent.md` and the four-class
result, this shows that a still-failing fourteen-source pool with
at least five opposite sources, all opposite multiplicities at most
two, must have **every adjacent tricolour class of size at most two**.
