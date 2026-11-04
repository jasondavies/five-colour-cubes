# Nine diffuse opposite sources suffice

**Status: elementary proof.** Any nine opposite-repeat sources, with
no variety occurring more than twice, assemble an opposite target.

As in the preceding notes, opposite varieties are the fifteen
undirected four-cycles of \(K_5\). Every edge gives both directed
corners. The proof uses the three-opposite-pairs lemma and the
neighbouring-pairs lemma, together with the incidence counts recorded
in `ten-opposite-sources.md`.

## 1. Zero, one, or at least three doubled varieties

If three varieties are doubled, use the three-pairs construction.

If there is exactly one doubled variety \(P\), choose target \(P\).
Each target edge has at least two neighbours. Its two-edge subsets
are avoided by five varieties, all single, and therefore have at
least \(9-5=4\) neighbours. Its three-edge subsets have at least
\(9-2=7\) neighbours. Hall holds.

If all nine sources are distinct, there are six omitted varieties.
At most one edge can have source frequency at most one: two such
edges would force at least \(5+5-2=8\) omitted varieties. Choose a
target avoiding that edge. Its individual edges then have at least
two neighbours, its pairs have at least four, and its triples at
least seven. Hall holds again.

## 2. Two doubled varieties

Let \(P,Q\) be the doubled varieties; the other five sources have
distinct varieties. If \(P,Q\) share two undirected edges, the
neighbouring-pairs lemma already gives an eight-source assembly.
Suppose therefore that \(P\cap Q=\{e\}\) is one edge.

Consider target \(P\). Its own two copies satisfy every one-edge
Hall inequality. At most three sources can avoid a triple of target
edges: the two possible avoiding varieties can include \(Q\) twice
and one single. Hence each triple meets at least six sources. The
full target meets all nine sources.

Thus \(P\) can fail only on a two-edge set \(F\subset P\), met
by at most three sources. Exactly five opposite varieties avoid
\(F\). To have six avoiding source copies, all five varieties must
be present and one must be \(Q\), doubled. Consequently

\[
F\subset P\setminus Q,
\]

and four of the five single varieties avoid \(F\). If target
\(Q\) also fails, there is likewise a two-edge set
\(G\subset Q\setminus P\), avoided by \(P\) and four of the
five single varieties.

The two four-element sets of single avoiders intersect in at least
three varieties. These three four-cycles avoid \(F\cup G\).
The sets \(F,G\) are disjoint, so their complement in \(K_5\)
is a six-edge graph \(L\).

## 3. The six-edge graph is a line union

The graph \(L\) contains at least three distinct four-cycles. Two
distinct four-cycles on five vertices share at most two edges. Since
their union lies in a six-edge graph, they must share exactly two,
and their union equals \(L\).

There are exactly two possibilities. If their common two edges are
disjoint, their union is \(K_4\). If their common two edges are
adjacent, their union is \(K_{2,3}\). In each case the union contains
exactly three four-cycles: the two given ones and their symmetric
difference. Thus the three common avoiders are precisely the three
line varieties in \(L\), and all occur as single source copies.

The source \(P\) has exactly two edges outside \(L\), namely
\(F\); \(Q\) has the complementary two outside edges \(G\).
Their two-edge intersections with \(L\) share the edge \(e\).
We now show that some line target \(T\subset L\) contains both
of those two-edge intersections.

### K4 line union

Let \(L\) be the complete graph on \(1,2,3,4\); its complement
is the star at colour 0. Since \(F,G\) partition the four star
edges, relabel so that

\[
P=\{01,02,13,23\},\qquad
Q=\{03,04,13,14\}.
\]

To justify the normal form, \(P\)'s two star edges have endpoints
1 and 2, and its fourth vertex may be called 3. The other two star
edges belong to \(Q\), whose fourth vertex is 1 or 2; exchange those
two labels if necessary. The target

\[
T=\{13,23,24,14\}
\]

contains \(P\cap L=\{13,23\}\) and
\(Q\cap L=\{13,14\}\).

### K2,3 line union

Let \(L\) have parts \(\{0,1\}\) and \(\{2,3,4\}\). Its
complement consists of edge \(01\) and triangle \(234\). Exactly
one of \(F,G\), say \(F\), contains \(01\). Relabel the three
other colours so that

\[
F=\{01,23\},\qquad G=\{24,34\}.
\]

The cycle \(P\) closes the two disjoint edges of \(F\) with
\(02,13\) or \(03,12\); choose the former by exchanging 2 and 3.
The cycle \(Q\) closes the path \(2,4,3\) through colour 0 or 1.
The simultaneous exchanges \(0\leftrightarrow1\) and
\(2\leftrightarrow3\) preserve \(P\), so choose colour 0. Hence

\[
P=\{01,23,02,13\},\qquad
Q=\{24,34,02,03\}.
\]

The line target

\[
T=\{02,03,12,13\}
\]

contains both \(P\cap L=\{02,13\}\) and
\(Q\cap L=\{02,03\}\).

## 4. A seven-source completion

Take the seven-source core consisting of the two \(P\) copies,
the two \(Q\) copies, and the three single line varieties. Every
source sees at least two undirected edges of the selected target
\(T\). Every target edge belongs to two of the three line varieties,
so it has at least two source neighbours.

These seven sources can fill any seven of the target's eight corners.
For Hall, a set using one target edge has at least two neighbours.
A set using two target edges has at least five: the only variety that
can avoid both while seeing at least two target edges is the unique
variety whose intersection is the complementary two-edge set, and
it occurs at most twice. A set using three target edges sees all
seven sources. The same is true for all four edges, and only seven
positions need to be filled.

Use either remaining opposite source at any compatible target
corner. The seven-source core fills the other seven corners. This
completes the nine-source proof.

## Consequence for the fourteen-source gap

After the earlier triple-adjacent-class lemmas, any still-failing
fourteen-source pool with at least five opposite sources has every
adjacent class of size at most two. The present theorem further
reduces the unresolved opposite totals to

\[
o=5,6,7,8.
\]

No claim is made here that these four remaining totals are settled.
