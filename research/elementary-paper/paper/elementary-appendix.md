---
title: "Mathematical appendix to Sharp thresholds for five-colour cube assemblies"
author: "Jason Davies"
date: "Consolidation draft, 4 November 2026"
geometry: margin=22mm
fontsize: 10pt
mainfont: DejaVu Serif
monofont: DejaVu Sans Mono
---

# Reading this mathematical appendix

This appendix is an integral mathematical part of the article, intended for
refereeing with it. It contains the longer corner arguments used by the direct
fifteen-source proof. The alternative certificate proof, executable audits,
and Lean implementation are described separately.

**Editorial status.** This is a consolidation draft. The arguments have been
collected and cross-linked from the proof-development notes. A final editorial
pass is still needed to shorten repetitions and standardise all local notation.
No claim is made that this appendix follows the existing Lean proof route.

A directed corner $ab$ abbreviates the complementary cyclic tricoloured corner.
$C(S)=S\to V\setminus S$, where $V=\{0,1,2,3,4\}$, is an adjacent class.
Its pole pair is the two-element side, and a repeated colour lies outside that
pair. An opposite variety supplies both directions of the edges of a four-cycle.
Every multiplicity refers to physical source copies. Hall matchings select
distinct copies; repeated entries assigned to one variety use separate copies.
An *own loop* in the arguments below is the article's *own completion*: a
matching of the six tricoloured corners after two class copies are reserved.

Arguments are ordered so that the recorded dependencies precede their uses.
This includes explicit file references and the implicit dependencies reviewed
in the bounded simplification pass; it is not a certification that every
implicit dependency has been found. Internal divisions retain local numbers: “Section 3” means local
division 3 of that argument unless another argument is named. Links to another
argument replace the research filenames. The prescribed-family eight-plus-three
lemma is proved in the main article's shared geometric tools, independently of
the corner threshold.

The proof uses mathematical case exhaustion and the displayed Hall tables.
Programs used to discover or audit these tables are not premises of the proof.


## Opposite-variety names

The local names $O_{60},\ldots,O_{74}$ (also printed O60, etc.) denote the following bidirected four-cycles. Each row means all edges joining the two displayed pairs; the remaining colour is repeated.

| Name | Repeated colour | Bipartition |
|---|---:|---|
| O60 | 0 | 12 / 34 |
| O61 | 0 | 13 / 24 |
| O62 | 0 | 14 / 23 |
| O63 | 1 | 02 / 34 |
| O64 | 1 | 03 / 24 |
| O65 | 1 | 04 / 23 |
| O66 | 2 | 01 / 34 |
| O67 | 2 | 03 / 14 |
| O68 | 2 | 04 / 13 |
| O69 | 3 | 01 / 24 |
| O70 | 3 | 02 / 14 |
| O71 | 3 | 04 / 12 |
| O72 | 4 | 01 / 23 |
| O73 | 4 | 02 / 13 |
| O74 | 4 | 03 / 12 |


# Argument 1: Cut intersections on an opposite target {#arg-1}

## 1. Two elementary facts about adjacent cuts on an opposite target {.unnumbered}

Fix an opposite target T. Every adjacent class meets T in two or four
directed positions, on two or four underlying edges respectively.
It never contains both directions of an edge.

At most two adjacent classes have their T-intersection inside any
specified two-position set. A two-position pattern is either a star,
which determines the class uniquely, or two opposite edges, with the
fifth colour free to join either side, which gives two classes.

At most three adjacent classes have their T-intersection inside a
specified three-position set. To see this, no four-position pattern
fits there. If two positions are the reverse directions of an edge,
the only possible two-position patterns pair the third position with
one of them, giving at most two classes. Otherwise the three positions
lie on a three-edge path in the target four-cycle. The two end edges
can give one opposite-edge pattern, with two classes. When that pattern
is valid, the middle position forms a valid directed star with at most
one end, adding at most one class. If the end-edge pattern is invalid,
only the two possible stars remain. The bound is three in all cases.

In particular, ten adjacent sources with class cap three cannot all
have their target intersections inside three positions.




# Argument 2: Five opposite sources with two neighbouring pairs {#arg-2}

**Lemma.** Let \(P,Q\) be opposite varieties sharing four directed
corners, and let \(R\) be any other opposite variety. The sources

\[
2P+2Q+R+2A+B
\]

assemble an opposite target whenever \(A,B\) are different adjacent
tricolour classes.

Write

\[
I=P\cap Q,\qquad J=P\setminus Q,\qquad K=Q\setminus P,
\qquad T=P\mathbin\triangle Q.
\]

Here \(I,J,K\) are two-edge sets, with each edge denoting both of its
directed corners. The line targets are \(P=I\cup J\),
\(Q=I\cup K\), and \(T=J\cup K\). Their union is a bidirected
\(K_4\) or \(K_{2,3}\).

## 1. Adjacent restrictions to a line {.unnumbered}

An adjacent cut uses at most one direction of an undirected edge.
It therefore meets each of \(I,J,K\) in at most two positions.
Its intersection with any opposite target has size two or four.
Consequently its three block counts are precisely one of

\[
(1,1,1),\qquad (2,2,0)\text{ and its permutations},\qquad (2,2,2).
\]

Moreover a restriction with counts \((1,1,1)\) determines the
adjacent class uniquely. On a \(K_4\) line union its three cut edges
form a directed star; their orientation fixes the cut on the four
vertices, and the fifth colour must join the singleton side to make
the side sizes two and three. On a \(K_{2,3}\) line union a three-edge
cut meets all five vertices, so its directions determine both sides
of the cut.

For \(R\) outside the line, exactly one of \(P,Q,T\) is its high
target: its intersections with the line targets have two, one and
one undirected edges respectively. We consider its high target first.

## 2. R has high target P or Q, or R=T {.unnumbered}

Interchange \(P,Q\) if necessary to make the high target \(P\).
The five opposite sources can fill the five unreserved target corners
whenever the three holes reserved for the adjacent sources satisfy
one of these conditions:

| Target | Sufficient distribution of the three holes |
|---|---|
| \(P=I\cup J\) | At least one hole in \(J\) |
| \(Q=I\cup K\) | At least two holes in \(K\) |
| \(T=J\cup K\) | One hole in \(J\), two in \(K\) |

These rules follow directly by allocating the two copies confined to
one block first. On \(P\), the two \(Q\) copies require two \(I\)
positions; \(R\) sees an edge in each of \(I,J\), and the two \(P\)
copies are universal. If exactly one hole lies in \(J\), then
\(R\) and the two \(P\) copies fill its three remaining positions.
If two or three holes lie in \(J\), its remaining positions use
\(P\) copies, while \(R\) fills an available \(I\) corner.
On \(Q\), \(R\) sees one \(I\) edge, and the two or three holes
in \(K\) leave that edge available. On \(T\), the two \(P\)
copies and \(R\) fill the three remaining \(J\) positions, and the
two \(Q\) copies fill \(K\). The same three sufficient rules hold
when \(R=T\): on \(P\), assign \(R\) an available \(J\)
position, the two \(Q\) copies to \(I\), and the two universal
\(P\) copies to the remainder. The inequality on the holes leaves
at least one \(J\) and two \(I\) positions. The argument on
\(Q\) is symmetric, and on \(T\) the source \(R\) is universal.

If \(A\) has block counts \((1,1,1)\), write its corners as
\(a_I,a_J,a_K\). If \(B\) has a \(P\)-corner outside
\(\{a_I,a_J\}\), reserve those two corners for the \(A\) copies
and the new corner for \(B\); the first rule applies. Otherwise
\(B\)'s \(P\)-intersection is exactly \(\{a_I,a_J\}\), and
its block counts must also be \((1,1,1)\). If its \(K\) corner
differs from \(a_K\), reserve \(a_I,a_K\) and that new \(K\)
corner on \(Q\); the second rule applies. If it does not differ,
the two classes have the same three-corner restriction and hence are
equal, contrary to the hypothesis.

If \(A\) has two corners in both \(I,J\), use target \(P\).
The two \(A\) copies can choose distinct corners, including a
\(J\) corner, while avoiding any selected \(B\) corner.

If \(A\) has counts \((2,0,2)\), use \(P\) with the two
\(A\) holes in \(I\) when \(B\) has a \(J\) corner. Otherwise
\(B\) also has counts \((2,0,2)\); use \(Q\) with the two
\(A\) holes in \(K\) and a \(B\) hole in \(I\).

Finally suppose \(A\) has counts \((0,2,2)\). If \(B\) has
an \(I\) corner, use \(P\) with the two \(A\) holes in \(J\).
Otherwise \(B\) also has counts \((0,2,2)\); use \(T\) with
the two \(A\) holes in \(K\) and a \(B\) hole in \(J\).
This exhausts all adjacent block profiles.

## 3. R has high target T {.unnumbered}

Now \(R\) sees an edge in each of \(J,K\), and one edge in each
of the targets \(P,Q\). The following three completion rules suffice:

| Target | Sufficient distribution of the three holes |
|---|---|
| \(P\) | Two in \(I\), one in \(J\) |
| \(Q\) | Two in \(I\), one in \(K\) |
| \(T\) | At least one in each of \(J,K\) |

For the first rule, the two \(Q\) copies fill the two remaining
\(I\) positions; \(R\) and the two \(P\) copies fill the
three \(J\) positions. Only one \(J\) corner has been removed,
so \(R\)'s two-corner intersection there survives. The second
rule is symmetric. In the third rule the remaining block sizes are
three and two, and \(R\) joins the doubled variety on the larger
block. Again only one corner of that block was removed.

If \(A\) has counts \((1,1,1)\), first use \(T\). The two
\(A\) holes occupy its distinct \(J,K\) corners. Any new
\(B\) corner there gives the third hole and completes the assembly.
Otherwise \(B\) agrees on both corners and has profile
\((1,1,1)\). Since \(B\ne A\), uniqueness forces a different
\(I\) corner. On \(P\), use the two different \(I\) corners
and the \(A\) corner in \(J\).

If \(A\) has two corners in both \(J,K\), use \(T\), choosing
one \(A\) hole in each block while avoiding the chosen \(B\)
hole. If \(A\) has counts \((2,0,2)\), a \(B\) corner in
\(J\) permits two \(A\) holes in \(K\) on \(T\). If no
such corner exists, \(B\) also has profile \((2,0,2)\); use the
two \(A\) corners in \(I\) and one \(B\) corner in \(K\)
on \(Q\). The profile \((2,2,0)\) is symmetric. All cases
are now covered.

## Consequence {.unnumbered}

In a fourteen-pool with five diffuse opposite sources and an adjacent
class of size at least three, the opposite profile \(2,2,1\) is
settled whenever the doubled varieties share four directed corners.
There are other adjacent classes available, since the adjacent total
is nine and each class has multiplicity at most three after the
four-class case is removed. Select two copies of the triple class
and one source from another class, then apply the lemma.



# Argument 3: Two four-cycle line normal forms {#arg-3}

## 3. The six-edge graph is a line union {.unnumbered}

Let \(P,Q\) be four-cycles sharing exactly one edge \(e\). Let disjoint two-edge sets \(F\subset P\setminus Q\) and \(G\subset Q\setminus P\) have six-edge complement \(L\) in \(K_5\). Suppose \(L\) contains at least two distinct four-cycles. Two
distinct four-cycles on five vertices share at most two edges. Since
their union lies in a six-edge graph, they must share exactly two,
and their union equals \(L\).

There are exactly two possibilities. If their common two edges are
disjoint, their union is \(K_4\). If their common two edges are
adjacent, their union is \(K_{2,3}\). In each case the union contains
exactly three four-cycles: the two given ones and their symmetric
difference. 

The source \(P\) has exactly two edges outside \(L\), namely
\(F\); \(Q\) has the complementary two outside edges \(G\).
Their two-edge intersections with \(L\) share the edge \(e\).
We now show that some line target \(T\subset L\) contains both
of those two-edge intersections.

### K4 line union {.unnumbered}

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

### K2,3 line union {.unnumbered}

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




# Argument 4: Six diffuse opposite cubes and three cubes in one adjacent class {#arg-4}

**Lemma.** Six opposite-repeat sources, with no opposite variety occurring
more than twice, together with three sources from one adjacent tricolour
class, always assemble an opposite target. Thus nine sources suffice.

The repeated colours of the three adjacent sources are irrelevant.

## 1. The two-by-three grid {.unnumbered}

Normalize the adjacent class to

\[
A=\{0,1\}\longrightarrow\{2,3,4\}.
\]

Its six directed corners are a grid with two rows and three columns.
Each opposite source meets this grid in one of the following fifteen
patterns:

* two positions in different columns, one position in each; there are
  twelve such patterns;
* a complete two-column rectangle; there are three such patterns.

Each pattern determines the opposite variety uniquely. In particular
every pattern meets exactly two columns. An opposite source has the
reversed versions of the same corners as well.

Let \(r(X)\) be the maximum number of corners in a grid subset \(X\)
that can be assigned to different opposite sources. This is the rank
function of a transversal matroid.

If some two-column rectangle has rank four, assign four opposite
sources to its four reverse corners. Any unused opposite source meets
the forward rectangle: it meets two of the three columns, so at least
one of the selected two. That source and the three \(A\) sources fill
the four forward positions. We have an opposite assembly.

We may therefore suppose that all three two-column rectangles have
rank at most three. If the columns are \(X,Y,Z\), submodularity gives

\[
2r(X\cup Y\cup Z)
\le r(X\cup Y)+r(X\cup Z)+r(Y\cup Z)\le9.
\]

Consequently the six-corner grid has matching rank at most four.

## 2. A Hall cover with at most four positions {.unnumbered}

By the matching-rank form of Hall's theorem, there is a grid subset
\(H\) such that

\[
|H|+\#\{\text{opposite sources whose pattern is not contained in }H\}
\le4.
\]

We may take \(|H|\le4\). A set of at most one position contains no
opposite pattern. A two-position set contains at most one variety,
hence at most two of the six sources. Those cases contradict the
displayed inequality. Thus only the following possibilities remain:

1. \(|H|=3\), and at least five of the six sources have patterns in \(H\);
2. \(|H|=4\), and all six source patterns lie in \(H\).

### Three positions {.unnumbered}

If the three positions use only two columns, they contain just two
opposite patterns, allowing at most four sources. Hence they occupy
three different columns. Their three two-position subsets are the
only available patterns.

The corresponding three opposite varieties share four corners
pairwise. This can be seen by closing each two-edge path or matching
to its unique opposite four-cycle; the three cycles form one of the
lines described in the neighbouring-pairs lemma. Equivalently, up to
row exchange and column permutations the grid positions are either
\(02,03,04\) or \(02,03,14\). The varieties in the first case are
\(O63,O64,O65\), and in the second case \(O65,O68,O71\); each pair
has four corners in common.

At least five copies among these three varieties, each with capacity
two, force two doubled varieties. These are neighbouring opposite
varieties. The other two opposite sources and any two of the adjacent
sources now give the neighbouring-pairs construction.

### Four positions in two columns {.unnumbered}

Here \(H\) is a complete rectangle. Its six opposite sources must
match all four positions. To see this directly, an absent position
would confine all six sources to the other three positions, which
contain only two varieties and hence at most four sources. A deficient
pair of positions would confine at least five sources to the other
two, which contain at most one variety and hence two sources. A
deficient triple would confine at least four sources to one position,
which contains no pattern. Hall's remaining inequality is immediate.

This contradicts our assumption that every rectangle has rank at most
three.

## 3. Four positions in all three columns {.unnumbered}

The remaining shape has two positions in one column and one in each
of the other columns. It contains exactly five opposite patterns:
the five two-position pairs lying in different columns. Let \(T\)
be the opposite variety determined by the two singleton-column
positions.

Two elementary facts about these five varieties finish the proof:

* each of them shares at least two undirected corner edges with \(T\);
* each undirected edge of \(T\) is absent from exactly two of the five
  varieties.

There are only two grid shapes up to row exchange and column
permutation. The following table verifies both facts explicitly.
An undirected edge denotes its two directed corners. The last column
lists, for each edge of \(T\), the three varieties containing it.

| Grid positions \(H\) | Five varieties | Central target \(T\) | Edge supports within the five varieties |
|---|---|---|---|
| \(02,12,03,04\) | \(63,64,65,70,73\) | \(63=\{03,04,23,24\}\) | \(03:63,65,73;\quad04:63,64,70;\quad23:63,64,73;\quad24:63,65,70\) |
| \(02,12,03,14\) | \(61,65,68,71,73\) | \(68=\{01,03,14,34\}\) | \(01:68,71,73;\quad03:65,68,73;\quad14:61,68,71;\quad34:61,65,68\) |

For self-contained decoding, the varieties appearing in this table
have the following undirected edge sets:

\[
\begin{array}{c|l@{\qquad}c|l}
61&12,14,23,34&63&03,04,23,24\\
64&02,04,23,34&65&02,03,24,34\\
68&01,03,14,34&70&01,04,12,24\\
71&01,02,14,24&73&01,03,12,23.
\end{array}
\]

Since there are six opposite sources and each variety occurs at most
twice, the two varieties missing any given target edge account for at
most four sources. Every edge of \(T\) therefore has at least two
source copies available. Each source meets at least two edges of
\(T\). The robust-six criterion from the neighbouring-pairs note
applies: the six sources can fill any six of its eight corners.

Two adjacent sources can choose distinct compatible corners of
\(T\), since each has at least two. Fill the remaining six corners
with the opposite sources. This proves the lemma.

## Consequences and an independent check {.unnumbered}

In the diffuse fourteen-source problem, a pool with at least six
opposite sources and an adjacent class of multiplicity at least three
is soluble. Thus, after this lemma, any remaining failure with six or
more opposite sources has every adjacent class of size at most two.

The standalone checker `sixO_threeA.cpp` independently checks every
six-opposite inventory with multiplicity at most two against a fixed
adjacent class. Colour permutation and reversal cover all classes.
Its output is:

```
Checked 28665; no exception
```

This check is a verification of the statement, separate from the
elementary proof above.



# Argument 5: Five opposite sources with two nonneighbouring pairs {#arg-5}

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

## 1. Two possible grid shapes {.unnumbered}

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

## 2. Overlapping patterns {.unnumbered}

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

## 3. Disjoint patterns: two explicit ways to complete {.unnumbered}

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

## Combined consequence {.unnumbered}

Together with [Argument 4](#arg-4) and the four-class
result, this shows that a still-failing fourteen-source pool with
at least five opposite sources, all opposite multiplicities at most
two, must have **every adjacent tricolour class of size at most two**.



# Argument 6: Five opposite cubes, one doubled variety, and a triple adjacent class {#arg-6}

**Lemma.** A fourteen-source pool is soluble if it has exactly five
opposite sources, at most one opposite variety is repeated, every
opposite variety occurs at most twice, and one adjacent tricolour
class has at least three copies. Here we may assume that every adjacent
class has at most three copies, since the four-class case is already
settled separately.

Only opposite targets are used. The opposite inventory has profile
\(1^5\) or \(2,1,1,1\).

## 1. The grid cover {.unnumbered}

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

## 2. Selecting a target {.unnumbered}

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

## 3. Five-source completion after the two A corners are reserved {.unnumbered}

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

## 4. An additional adjacent source exists {.unnumbered}

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

## Remaining five-opposite profile {.unnumbered}

The argument leaves only opposite inventory \(2,2,1\). A separate
line-hole construction handles the case in which the two doubled
varieties share four directed corners. The remaining case with two doubled opposite varieties sharing only
two directed corners is proved separately in
[Argument 5](#arg-5).



# Argument 7: Three opposite pairs and two arbitrary sources {#arg-7}

**Proved elementary lemma.** Two copies of each of any three distinct
opposite-repeat varieties, together with any two further five-colour
cubes, admit an opposite-repeat corner assembly.

There is no multiplicity restriction on the two additional cubes.
This is stronger than the corresponding special case of the earlier
finite eight-cube lemma. It does not settle all its six-opposite cases.

## 1. Undirected notation and a robust-six observation {.unnumbered}

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

## 2. When a robust-six target exists {.unnumbered}

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

## 3. The remaining normal form {.unnumbered}

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

### Two adjacent additional sources {.unnumbered}

The first two paths H are complementary edge sets in the complete graph
on {0,2,3,4}. A two-three cut splits these four vertices nontrivially,
and therefore crosses three or four of that complete graph's edges.
It consequently meets at least one of these two paths in at least two
corners. The other adjacent source meets that path in at least one
corner. Assign the sources to two distinct corners of H and complete
with the six opposite copies.

### One adjacent and one opposite additional source {.unnumbered}

The two sets {Z,V} and {X,W} in the first two rows are disjoint.
Thus the additional opposite source meets H in at least one of these
rows, giving it at least two directed corners there. The adjacent
source has at least one corner there. Again distinct holes can be
assigned and the core completes the assembly.

### Two opposite additional sources {.unnumbered}

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

## Consequence {.unnumbered}

A failing pool of size at least eight cannot contain three distinct
opposite varieties twice each. In particular, in the remaining diffuse
fourteen-cube branch, at most two opposite varieties can occur twice.
An elementary treatment of six-opposite cores with multiplicity profiles
(2,2,1,1), (2,1,1,1,1), or(1,1,1,1,1,1) is still needed for the full
eight-cube lemma.




# Argument 8: Two neighbouring opposite pairs and two further opposite sources {#arg-8}

**Proved elementary lemma.** Let A,B be distinct opposite varieties
sharing four directed corners, equivalently two undirected edges.
Take two copies of each. Add two opposite sources C,D, neither of
which is A or B (they may equal each other), and any two further
five-colour cubes. These eight sources have an opposite-target assembly.

The proof uses the three-opposite-pairs lemma in the companion note.
There is no multiplicity restriction on the two arbitrary sources.

## 1. The line of three four-cycles {.unnumbered}

Use undirected four-cycle notation, with each edge denoting both
directed corners. Put

    I=A∩B, J=A\B, K=B\A, T=A symmetric-difference B=J∪K.

Each of I,J,K has two edges, and T is a four-cycle. The three cycles
A=I∪J, B=I∪K, T=J∪K form a line: their union is either K4 (when
I consists of disjoint edges) or K2,3 (when I consists of adjacent edges).
Each union edge occurs in exactly two of the three cycles.

Every opposite variety E outside {A,B,T} has two edges in this union.
For a K4 union this follows because E uses the fifth vertex, leaving
only a two-edge path on the other three vertices. For a K2,3 union,
the number of crossing edges in the four-cycle E is even; it cannot
be zero, and if it were four E would be one of A,B,T. Thus it is two.

Since E meets each of A,B,T in at least one edge, its intersection
sizes with the three are therefore (2,1,1) in some order. Call the
cycle with intersection size two its high target. More precisely,

* high A: one edge of I and one of J;
* high B: one edge of I and one of K;
* high T: one edge of J and one of K.

## 2. A robust-six criterion {.unnumbered}

Six opposite sources, with every variety occurring at most twice, can
fill any six corners of a target E if:

* each source intersects E in at least two undirected edges;
* each edge of E is present in at least two source copies.

For Hall's theorem, one edge pair has at least two neighbours. A set
meeting two target edges has at least four: only one opposite variety
can have its E-intersection confined to the complementary two edges,
and that variety has at most two copies. A set meeting at least three
target edges sees all six sources. Thus every set of at most six
positions has enough neighbours.

If C or D equals T, or if C,D have the same high target, this criterion
immediately supplies the needed robust-six target. At A or B the two
copies of that variety provide the edge-frequency bound; at T the
two A and two B copies provide it because J and K partition T.
The arbitrary additional sources can then fill any two distinct
compatible corners.

It remains that C,D have different high targets.

## 3. Two elementary six-corner completion rules {.unnumbered}

The following rules are useful on target A=I∪J. Its source pattern
consists of two universal A copies, two B copies seeing I, one C
copy seeing one edge of I and one edge of J, and one other source D.

**Rule I.** If D sees one edge of I, the six sources can fill every
six-position set whose two omitted corners are not both in I.

If one omitted corner is in I and one in J, the remaining three J
corners are filled by C and the two A copies: C's two J corners
cannot both be omitted. The three remaining I corners are filled
by D and the two B copies. If both omitted corners are in J, the
two A copies fill the two remaining J positions. C,D can be assigned
distinct I corners (each has two), and the two B copies fill the rest.

**Rule II.** If D sees the single edge e in J, the six sources can
fill every six-position set unless the omitted pair consists of
both directions of e.

Assign D an available e corner. If three J positions remain, neither
omitted corner was in J; C still has a J corner and it joins the
two A copies there. The two B copies fill the two remaining I
positions. If two J positions remain, use the two A there, and
C plus two B at the three remaining I positions. If one J position
remains, use one A there and the other A, C and two B at the four
I positions. Every stated assignment has a compatible corner.

## 4. Different high targets {.unnumbered}

First suppose C has high target A and D high target B. On target A,
D sees one edge of I, so Rule I applies. On target B the symmetric
Rule I applies. Every additional cube has a corner of the opposite
target T=J∪K. If that corner is in J, reserve it as a hole in A;
if it is in K, reserve it as a hole in B. The other additional cube
has at least two corners of the selected target and hence can fill
a different position. The omitted pair is not confined to I, so
the corresponding six-corner completion works.

Next suppose C has high target A and D high target T. On target A,
D sees an edge e of J, so Rule II applies. It yields an assembly
unless both additional cubes have all their A-compatible corners
inside the bidirected edge e.

An adjacent cut cannot have this property: it has at least two
corners of A, on distinct undirected edges. Both additional sources
would therefore be opposite varieties whose intersection with A is
exactly e. There are precisely two such varieties; one is D, and
write R for the other. (They are obtained by omitting one or the
other of A's vertices not on e.)

If an additional source is D, the pool contains two copies each
of A,B,D. If neither is D, both are R, and it contains two copies
each of A,B,R. In either case the three-opposite-pairs lemma applies.

The case of high targets B and T is symmetric. These exhaust the
possibilities, proving the lemma.

## Consequence for the diffuse fourteen-cube problem {.unnumbered}

If a pool has at least six opposite sources, every opposite variety
occurs at most twice, and two doubled varieties share four corners,
it is soluble. Choose those four sources, any two other opposite
sources, and any two further sources.

Combining this with the three-opposite-pairs lemma, a still-failing
pool with at least six opposite sources could have at most two
doubled opposite varieties; if it has two, they must share only
two corners. The cases with two such nonneighbouring doubled types,
one doubled type, or no doubled type are not settled by this note.




# Argument 9: Avoided edges and common high targets {#arg-9}

## 1. Three basic facts about the adjacent pool {.unnumbered}

The following statements hold in a pool with no opposite assembly.

### Nine adjacent cubes cannot all avoid two edges {.unnumbered}

If the two edges meet, a cut avoiding both must keep all three of
their vertices together. Only two reverse adjacent classes do this,
with combined capacity six, which cannot accommodate nine cubes.

If the edges are disjoint, each endpoint pair stays together. The
pairs lie on opposite sides of the cut; the fifth colour may join
either side. Thus there are four possible classes, two in each
orientation between the pairs, with capacity six per orientation.
Nine cubes split with at least three in each orientation. Four cubes
in each orientation would fill an opposite target between the pairs.
If one orientation has only three, use four cubes from the other
orientation and those three, together with any opposite source in
the remaining position. An opposite source meets that target in at
least one underlying edge and supports its required direction. Again
there is an assembly.

## 3. A common high target always exists {.unnumbered}

**Geometric lemma.** Any three distinct opposite varieties have an
opposite target on which all three are high.

If two of the varieties are neighbours (share two edges), they lie
on a line of three four-cycles inside a K4 or K2,3. If the third
variety is on that line, any line target works. If it is outside,
it meets exactly one line target in two edges and the others in one;
choose its high line target. This is the elementary line geometry
in [Argument 8](#arg-8).

Moreover this target is fully supported by the first two varieties:
it is either one of them, or their symmetric difference. 

It remains to consider three pairwise nonneighbouring varieties.
Normalize the doubled variety and one single to

    D=O60={13,14,23,24}, P=O67={01,04,13,34}.

A variety meeting both only in one edge has exactly four possibilities:

| Other single Q | Edges of Q | A common high target | Edge of target absent from D∪P∪Q |
| --- | --- | --- | --- |
| O65 | 02,03,24,34 | O62={12,13,24,34} | 12 |
| O69 | 02,04,12,14 | O66={03,04,13,14} | 03 |
| O72 | 02,03,12,13 | O62={12,13,24,34} | none |
| O73 | 01,03,12,23 | O74={01,02,13,23} | 02 |

Here is a direct completeness check. If Q contains the common edge13,
it must avoid all other edges of D∪P, which uniquely gives O72.
Otherwise it uses one edge from D\P, one from P\D, and two edges
of the missing path1–2–0–3. Choose the latter two edges. If they
meet, closing their two-edge path through the allowed fourth vertex
gives O65 or O69. If they are disjoint, the only allowed closure
gives O73. The alternative closure in each case uses edge13, which
is excluded. The table is therefore a four-cycle classification,
not a source-inventory search.

Direct intersection verifies the three high-target conditions in
every row. 




# Argument 10: Eight opposite-repeat cubes with multiplicity cap two {#arg-10}

**Theorem.** Any eight opposite-repeat five-colour cubes, with no variety
occurring more than twice, assemble an opposite-repeat target.

An opposite variety is an undirected four-cycle of K5; each edge gives
both directed corner positions. This proof uses the elementary three-
pairs and neighbouring-pairs constructions in `../opposite_small_lemma/`.
It uses the line geometry from [Argument 3](#arg-3), but does not
assume the numerical nine-source theorem or any exhaustive search.

## 1. Incidence facts and a five-source core {.unnumbered}

Every edge belongs to six opposite varieties. Every pair of distinct
edges belongs to two varieties, and is avoided by exactly five.
For a fixed target, each two-edge intersection belongs to exactly one
other variety; each one-edge intersection belongs to exactly two.

The five distinct varieties avoiding two fixed edges form a useful
core. They can fill any five corners of a suitable central target.
The following two normal forms cover adjacent and disjoint forbidden
edges. Each entry denotes a set of undirected edges.

| Forbidden pair F | Central target T | Intersections of the other four avoiders with T |
| --- | --- | --- |
| {01,02} | {13,14,23,24} | {14,23}; {13,24}; {23,24}; {13,14} |
| {01,23} | {02,03,12,13} | {12,13}; {02,03}; {03,13}; {02,12} |

Every target edge has three source neighbours. A corner set using two
edges has at least four neighbours, since only the unique variety with
the complementary two-edge intersection can avoid it. A set using
three edges sees all five sources. Hall therefore gives a matching
of any five target corners.

We need two elementary ways to fill the other three positions.

* Three distinct opposite varieties can match three corners of any
  target: each has at least two corners, and at most two varieties
  can have their entire intersection in one bidirected edge.
* Three opposite sources can also match three corners if one sees
  at least two target edges. Every two-source union has size at least
  two, while the three-source union then has size at least four.

Finally, any four-cycle containing the forbidden pair F meets its
central target T in two edges. For adjacent F, the cycle closes the
two-edge path through one other vertex, and its two closing edges
belong to T. For disjoint F, its other two edges join the two pairs
and likewise belong to T.

## 2. Zero or one doubled variety {.unnumbered}

### Eight distinct varieties {.unnumbered}

At most one undirected edge has source frequency at most one. Otherwise
two low-frequency edges would require at least5+5−2=8 omitted varieties,
whereas only seven varieties are omitted.

If the eight varieties contain all five avoiders of any two edges,
use their five-source core and the remaining three distinct sources.
Otherwise every two-edge target set has at least four neighbours:
a failure would require at least five sources avoiding those two edges.
Every three-edge target set has at least six neighbours, since only
two varieties avoid three edges of a four-cycle.

Choose a target avoiding the possible low-frequency edge. Its single
edges have at least two neighbours, its pairs at least four, its triples
at least six, and all four edges see all eight sources. These are all
Hall inequalities, proving the claim.

### One doubled variety P {.unnumbered}

Use P as target. Its own two copies satisfy the one-edge inequalities.
Any three target edges have at least six neighbours, because at most
two single varieties avoid them. Hence failure would require a pair
F⊂P having at most three neighbours. All five avoiding varieties must
then occur among the six distinct single sources.

Use their five-source core. The remaining sources are two P copies
and one single. P contains F, so it sees two edges of the central
target, by Section1. These three sources match three target corners,
and the five-source core fills the rest.

## 3. Three doubled varieties, or neighbouring doubled varieties {.unnumbered}

If at least three varieties are doubled, the three-pairs lemma assembles
using those six cubes and any two others.

If exactly two doubled varieties P,Q share two edges, the neighbouring-
pairs lemma applies to two copies of each, two further opposite sources,
and the two remaining sources.

The only remaining profile is 2P+2Q and four distinct single varieties,
with P,Q sharing exactly one edge e.

## 4. The one-edge companion is present {.unnumbered}

There is a unique variety V meeting both P and Q only at e. Normalize

    P={13,14,23,24},  Q={01,04,13,34},  V={02,03,12,13}.

Suppose V is one of the four single sources. The other three singles
are distinct and differ from P,Q,V. Consider these three targets:

| Target | P intersection | Q intersection | V intersection | V-private edge |
| --- | --- | --- | --- | --- |
| {12,13,24,34} | {13,24} | {13,34} | {13,12} | 12 |
| {03,04,13,14} | {13,14} | {13,04} | {13,03} | 03 |
| {01,02,13,23} | {13,23} | {13,01} | {13,02} | 02 |

**Claim.** Each target assembles as soon as an extra single source
contains its V-private edge.

Check source-side Hall. A union of one target edge can contain at most
two of the three extra singles and none of P,Q,V, so has at most two
sources. A union of two target edges can contain only one of the three
displayed anchor patterns. If it contains a P or Q pattern, it omits
the V-private edge and hence misses the extra source containing that
edge; it therefore contains at most two anchor copies and two extras.
If it contains the V pattern it contains at most one anchor copy and
three extras. In either case at most four sources are confined there.

A three-edge union can contain at most two anchor patterns. If they
are P,Q, it omits the V-private edge and therefore contains at most
four anchor copies and two extras. If one is V, it contains at most
three anchor copies and three extras. Thus at most six sources are
confined to three edges. All source-side Hall inequalities hold.

The only opposite varieties avoiding all three edges12,02,03 are P,Q.
Indeed those edges form the path1–2–0–3. Omitting an endpoint leaves
an internal vertex of degree one; omitting the isolated vertex4 leaves
only three allowed edges. Omitting either internal vertex gives the
unique avoiding four-cycle P or Q. Thus every extra single contains
at least one V-private edge in the table, and one target assembles.

## 5. The companion is absent {.unnumbered}

Use P as target. Single-edge Hall inequalities hold because P occurs
twice. Three-edge inequalities also hold: a three-edge complement could
have three avoiding copies only from Q,Q,V, and V is absent. Thus a
failed P target has a two-edge obstruction F⊂P∖Q, avoided by both Q
copies and at least three of the four singles.

If all four singles avoid F, they and one Q are precisely the five
distinct avoiding varieties. Their central target has a five-source
completion. The remaining sources are P,P,Q; the remaining Q sees
at least two target edges because it is one of the five avoiding
varieties. These three sources fill the other three corners.

We may therefore assume exactly three singles avoid F. Likewise, if
Q does not assemble, exactly three singles avoid a two-edge set
G⊂Q∖P. The sets F,G are disjoint, and their complement L in K5 has
six edges.

The two three-element sets of single avoiders have at least two members
in common. Thus L contains two distinct four-cycles. Their union must
have exactly six edges, and is either K4 or K2,3. It contains exactly
three four-cycles, the familiar line of opposite varieties.

There is a line target T containing both P∩L and Q∩L. Explicit normal
forms are:

| Line union L | P | Q | T | Edge h of T outside P∪Q |
| --- | --- | --- | --- | --- |
| K4 on1234 | {01,02,13,23} | {03,04,13,14} | {13,23,24,14} | 24 |
| K2,3 with parts01 and234 | {01,23,02,13} | {24,34,02,03} | {02,03,12,13} | 12 |

These are the two line normal forms justified in
[Argument 3](#arg-3), Section3.

If three single varieties avoid both F and G, all three line varieties
are present. Then 2P+2Q and those three line sources fill any seven
corners of T: a target edge has at least two neighbours, a pair has at
least five, and a triple sees all seven sources. The remaining single
completes the target.

Otherwise exactly two singles X,Y avoid both pairs. The other two,
R,S, satisfy

    R avoids G and meets F;    S avoids F and meets G.

In either normal form, the only four-cycle avoiding G and h while
meeting F is P itself. Since R differs from P, it must contain h.
For clarity, this small graph fact can be checked as follows.

* In the K4 form, avoiding G={03,04} leaves vertex0 with possible
  neighbours1,2. A cycle meeting F={01,02} must use both edges. Its
  other two edges close through3 or4; avoiding h=24 forces the
  route through3, which is P.
* In the K2,3 form, G={24,34} and h=12. A cycle using23 must also
  use02, because vertex2 then has only neighbours0,3; its only
  four-cycle closure is through13,01, giving P. A cycle using01
  must leave vertex1 through13 or14. The route through4 cannot
  return in two steps, since24,34 are forbidden; the route through3
  must use23,02. This again gives P.

Now consider the six-source core 2P+2Q+X+Y. Every source sees at least
two edges of T. Every target edge is covered by X or Y, because their
union is L. Three target edges also have P or Q copies, so their
frequencies are at least two. The remaining edge h acquires its second
neighbour from R.

A two-edge set has at least four neighbours already in the six-source
core: the only variety that can avoid it while meeting T in at least
two edges is the unique complementary-pair variety, with multiplicity
at most two. Every three-edge set sees all six core sources. All four
edges see all eight sources. Hall therefore gives a full assembly of T.

This completes all multiplicity profiles and proves the theorem.

## Consequence: seven opposite sources and any adjacent cube {.unnumbered}

**Corollary.** Seven opposite sources with multiplicity cap two, together
with any adjacent-repeat cube A, assemble an opposite target using all
eight cubes.

The directed cut of A contains the forward halves of three opposite
varieties, one for each choice of two columns. If all three varieties
are already doubled among the seven sources, the three-pairs lemma
applies, with the seventh opposite source and A as the two extras.

Otherwise choose one of these three varieties R that is not doubled.
Replace A temporarily by R. The eight opposite sources have cap two,
so the theorem supplies an assembly. Let c be the corner assigned to
the temporary R. Its underlying edge crosses the two parts of A, so
exactly one of c and its reverse belongs to A. If c belongs to A,
replace R by A directly. Otherwise reverse every directed corner
of the assignment. This preserves the target and every actual opposite
source, since their corner sets are bidirected; the reversed c now
belongs to A. Choosing compatible proper rotations realizes the new
assignment. This proves the corollary.




# Argument 11: Three opposite copies and the butterfly support {#arg-11}

This is a hand classification of the first four-corner Hall-cover orbit
for a fourteen-failure containing three identical opposite copies.
It uses the established adjacent-class bound five. Other Hall-cover
orbits are treated separately; this note does not assert completeness
of the full fourteen-failure classification.

Use O=±{13,14,23,24} and adjacent cuts

    H1=C(01), H2=C(02), H3=C(124), H4=C(123),
    U=C(12), V=C(012).

Let their counts be x1,x2,x3,x4,u,v, totaling eleven. The three copies
of O are additional. Put L=x1+x2+v, R=x3+x4+u, so L+R=11.

## Elementary assembly rules {.unnumbered}

1. If u≥4 or v≥4, two copies in that low class have the same repeated
   colour. Reserve them for the two bicoloured corners. Two further
   copies fill the two corners involving colour0. Three O and any
   remaining adjacent copy fill the other four corners. Thus u,v≤3.

2. If xi≥4 and its side total is at least six (L for i=1,2; R for
   i=3,4), reserve a same-repeat pair in Hi. Two remaining Hi copies
   fill its private pair of tricoloured corners. Two further copies
   from its side fill the other two corners outside O, and two O
   fill the last pair. For H1, these pairs are respectively
   {02,12}, {03,04}, and {13,14}.

3. If all four high classes are nonempty, form the opposite target
   ±{12,14,23,34}. One copy each of H1,H2,H3,H4 supplies
   12,21,43,34. Three O and one remaining adjacent copy fill
   14,41,23,32: every adjacent class in this family has 14 or23.

4. If exactly three high classes are nonempty, normalize x1=0.
   If x2+v≥2, build ±{03,04,23,24}: two copies from H2∪V supply
   03,04; H3,H4 supply40,30; three O and another adjacent copy
   supply23,32,24,42. Therefore failure forces x2=1,v=0.
   Then R=10 and u≤3, so one of x3,x4 is at least four;
   rule2 gives an assembly.

5. If exactly two high classes in the same block are nonempty,
   normalize these to H1,H2. If u≥2, build ±{01,02,14,24}:
   H2,H1 supply01,02, two U supply10,20, and three O plus one
   remaining adjacent copy supply14,41,24,42. Otherwise u≤1,
   L≥10 and v≤3, so one of x1,x2 is at least four; rule2 applies.

6. If at most one high class is nonempty, its bound five and u,v≤3
   force exactly the profile5,3,3; its side is at least eight,
   so rule2 again applies.

Consequently exactly two high classes, one from each block, are
nonempty. Normalize them to X=H1 and Y=H3, with counts x,y.

## Four numerical possibilities {.unnumbered}

We have x+y+u+v=11, x,y≤5 and u,v≤3. If x≥4, rule2 forces
x+v≤5, hence y+u≥6. If y≥4, rule2 would solve because its side
is at least six. Thus y≤3, and y=u=3, x+v=5. The symmetric
argument holds if y≥4. If both x,y≤3, the total forces three
counts3 and one count2.

Up to swapping the two sides, only the following possibilities remain:

| x | y | u | v |
|---|---|---|---|
| 2 | 3 | 3 | 3 |
| 3 | 3 | 2 | 3 |
| 3 | 4 | 1 | 3 |
| 3 | 5 | 0 | 3 |

## Repeated-colour pigeonhole {.unnumbered}

In all four rows, any two different nonempty classes among X,Y,U,V
must have disjoint sets of repeated colours. Otherwise their two
same-repeat cubes supply the bicoloured corners of an assemblable
target, as in this table:

| Reserved classes | Target cut |
|---|---|
| X,Y | Y in the first numerical row; X in the others |
| X,U | U |
| X,V | Y |
| Y,U | X |
| Y,V | Y |
| U,V | C(14) |

Here are explicit checks of the tricoloured completions. After the
reservations, X can be completed whenever at least two X copies and
at least four copies of X∪V remain: two X supply02,12; two further
X∪V supply03,04; and two O supply13,14. The corresponding rule for
Y requires two Y and four Y∪U, supplying40,43; 10,20; and13,23.
For target U, two Y∪U supply10,20, and three O plus any remaining
adjacent copy fill its four other corners. These numerical requirements
hold in every row where the indicated pair is present.

For the last pair U,V, their only possible common repeated colour is0.
Use their bicoloured corners with singleton1 and4. Three Y supply
10,40,43, one X supplies12, and two O supply13,42. This completes
the tricoloured cut C(14).

Moreover all copies within U have distinct repeated colours, and the
same holds within V. A same-repeat pair within U leaves at least two
Y∪U for its two corners involving0; three O and another adjacent
copy complete it. The analogous statement for V uses X∪V.

The number of distinct repeated colours required is therefore at
least 1+1+u+v. Only five colours exist. The first three rows require
8,7,6 respectively and are impossible. Only (x,y,u,v)=(3,5,0,3),
or its symmetric form (5,3,3,0), survives.

Hence every surviving coarse profile is three identical opposite
copies and adjacent-class sizes $5,3,3$. Only this necessary profile
is used in the threshold proof.



# Argument 12: Five copies in one class in an all-adjacent fourteen-pool {#arg-12}

**Theorem.** Fourteen adjacent-repeat cubes solve if some tricoloured
corner class occurs at least five times.

The six-class lemma already handles multiplicity at least six. Assume
a failing pool contains exactly five A=C(01), where C(S) denotes the
cut S→Sᶜ. Every adjacent class has count at most five.

The four classes disjoint from A are

    B=C(234), Z23=C(23), Z24=C(24), Z34=C(34).

Call their total z. Each has count at most three, since four A and four
copies of any one of these classes form an opposite target. Also z≤5:
six such disjoint sources match the six corners of C(234), and two
same-repeat A copies supply that target's bichromatic corners. This
six-corner matching follows from its three two-corner rows q→{0,1}:
B sees every row; each Z sees two; each missing-row class has count≤3.

Reserve a same-repeat pair among the five A for an A target's
bichromatic corners. The other three A can fill any three of its six
tricoloured corners. Therefore the nine outside sources have matching
rank at most two on A's six corners.

## 1. A useful eight-cube construction {.unnumbered}

Let D be a class meeting A in a single corner. Then

    4A + D + any three sources disjoint from A

has an opposite-target assembly.

To prove this, group the six corners of the reverse cut into the three
rows q→{0,1}, q=2,3,4. Each disjoint source sees all three rows or all
but one. D sees one corner in each of two different rows. We need a
four-position matching on two rows; four A then supply the forward half.

If two of the three disjoint sources miss the same row, choose the other
two rows. Those two sources are universal on the chosen half. D meets
it, and the third source has at least two corners in it, so D and that
source can be assigned distinct corners and the universal two finish.
If no missing row occurs twice, choose any two rows met by D. After D
fills a corner, the three other sources satisfy Hall on the other three:
each has a corner, any two see at least two, and all three see all three.

A related statement applies when a class T meets A in two corners of
one row of A. Such a T sees just one reverse corner, in some row q.
The same construction works unless all three disjoint sources are the
unique Z-class missing q. If two miss a different row, avoid that row;
if exactly two miss q, the third supplies the other corner of row q.
The case with no repeated missing row is as above.

## 2. Hall cover reduction {.unnumbered}

By Konig's theorem, matching rank at most two means that the nine
outside sources' incidences with A can be covered by at most two source
or corner vertices.

Two source vertices would leave at least seven disjoint sources,
contradicting z≤5. One corner plus one source vertex leaves at least
eight cubes in the union of the disjoint family and the unique class
D meeting A in that corner. Since D≤5, there are at least three
disjoint sources; since z≤5, D is nonempty. Section1 solves immediately.

It remains that all outside intersections lie in two A corners. Up to
the stabilizer of A, these form a column, a diagonal, or a row of its
two-by-three array.

## 3. Column and diagonal covers {.unnumbered}

For a column, normalize the two corners to03,13. The nonzero-intersection
classes are D0=C(024) and D1=C(124). If z≥3, Section1 solves. Otherwise
their counts total at least seven, so each is at least two. Four A,
two D0 and two D1 form the opposite target with partition01∣24:
A supplies02,04,12,14; D0 supplies21,41; D1 supplies20,40.

For a diagonal, normalize to03,14. The nonzero classes are
D0=C(024) and D1=C(123). Again z≤2. If both counts are at least three,
build the opposite target with partition04∣13:

    A:03,14; D0:01,41,43; D1:10,30,34.

Otherwise their counts are2 and5, and z=2. By symmetry D1 has count2.
If a disjoint source is B,Z23,orZ34, it supplies30 or34 in the displayed
target, leaving only two of D1's three positions. If instead the
disjoint sources are Z24, build the target01∣24 using

    A:02,04,12,14; D1:20; D0:21,41; Z24:40.

Thus column and diagonal covers always solve.

## 4. Row cover: numerical reduction {.unnumbered}

Normalize the row to13,14. Besides the disjoint sources, the allowed
outside classes are

    D=C(124), E=C(123), T=C(12),

with counts b,c,d. Thus b+c+d+z=9. The shared-four bounds give
b+d≤7 and c+d≤7.

If z≥3 and D or E is present, Section1 solves. If both are absent,
d≤5 forces z≥4. Choose three disjoint sources not all of the exceptional
type Z34; this is possible since each disjoint class has count≤3.
The second construction in Section1, applied to T, solves. Hence z≤2.

Suppose z=2. For a target with partition01∣24, four A supply the forward
half, one D supplies40, and another nonzero source supplies20. The two
disjoint copies can fill21,41 unless both are Z23 or both are Z34.
Similarly a target01∣23 works using E unless both disjoint copies are
Z24 or both are Z34. If both b,c are positive, the only shared exception
is two Z34, and then use target01∣34: four A supply its forward half,
D supplies40, E supplies30, and the two Z34 supply31,41. Thus that case
also solves. Since b+c+d=7>d's cap, at least one is positive. Up to
symmetry the only remaining forms have b>0,c=0, b+d=7, and either two
Z23 or two Z34.

If b≥4, reserve a same-repeat D pair. A disjoint source supplies20
(for Z23) or40 (for Z34); two remaining D supply the other one of20,40
and43; two T supply10,23; one A supplies13. If d≥4, reserve a
same-repeat T pair; two remaining T fill20,24, two D fill10,23, and
two A fill13,14.
Since b+d=7 and both are at most five, one of these constructions applies.

Consequently z≤1. A T-class of size at least four solves: reserve a
same-repeat pair, use two A at13,14, and match10,20,23,24 from the
remaining D,E,T copies. At least six such copies remain; 10 and20
see all of them, while23 and24 each see at least two.

Likewise b≥4 solves unless b=4,d=0. Reserve two D for the bichromatic
positions and two for40,43; use A at13. The three remaining positions
10,20,23 can be matched because the residual D+T count at23 is
b+d−4≥1 and at least four copies fit10,20. The symmetric statement
holds for E. If b=4,d=0, then c=5 when z=0 and the symmetric large-class
construction applies. When z=1, b=c=4. Every disjoint source meets at
least one of the private sets

    {23,40,43} for D,    {24,30,34} for E.

Use it there, two copies of the corresponding class at the other private
positions, two copies of the other class at10,20, and A at13 or14,
after reserving a same-repeat pair in the chosen four-copy class.

Thus every failure in this cover must satisfy b,c,d≤3. If z=0 then
b=c=d=3; if z=1 then (b,c,d) is a permutation of(3,3,2).

## 5. Row cover: repeated-colour contradiction {.unnumbered}

For all these residual counts, A,D,E,T are pairwise conflicting classes:
if two different classes share a repeated colour, a target can be
assembled. Also T has a loop: two T copies with the same repeat solve.
Here are direct verifications of these statements.

* A,D or A,E: reserve one from each for an A target. Four A fill
  02,03,04,12; remaining D,E,T copies fill13,14.
* D,E: use the target of a three-copy class among D,E, reserving one
  from each. Two remaining copies of that target class fill its private
  pair40,43 or30,34. The other three non-A positions are supplied by
  T and the other class; one A supplies13 or14. If d=2, both b,c=3,
  so T fills23 (or24) and one of10,20, while the other class fills
  the remaining one.
* A,T: use a T target. The reserved cubes supply poles1 and2. Two
  remaining A fill13,14; D,E,T match10,20,23,24.
* D,T or E,T: use an A target, with poles0 and1 supplied by those
  two classes. Four A fill its private corners and other copies fill13,14.
* Two T copies: use their T target. Two A fill13,14; D,E,T match the
  other four tricoloured corners. At least six copies remain in that pool.

The pole pairs are01,03,04,12 respectively. Therefore T uses d distinct
repeats, while each of A,D,E uses at least one, with all these colour
sets disjoint. This requires at least d+3 distinct colours. If d=3,
it requires six, impossible.

If d=2, then z=1 and b=c=3. The disjoint source meets40 or43, unless
it is Z23, in which case it meets30 and34. Consequently at least one
of D,E also has a loop: reserve two same-repeat cubes from that class,
use its last copy and the disjoint source for its two private corners,
T at23 or24, the other class at10,20, and A at13 or14.

But A,D,E are pairwise conflicting and all have pole0, so none may
repeat0. A looped three-copy class among D,E needs three of the other
four colours; each of the other two classes needs a different colour.
This requires five colours from a four-colour set, a contradiction.

All Hall-cover cases are therefore impossible. This proves the theorem.




# Argument 13: Six copies in one adjacent tricolour class {#arg-13}

This gives a self-contained hand proof of the concentration lemma used
elsewhere in the research notes.

**Lemma.** Every collection of fourteen five-colour cubes containing at
least six cubes from one adjacent tricoloured-corner class is soluble.

Write C(S) for the directed cut S→Sᶜ, where |S| is two or three. Its
pole pair is its two-element side. Its three varieties are indexed by
their repeated colour, which lies outside that pair. Two copies with
the same repeat supply both bicoloured corners of either orientation
of the cut with that pole pair.

Normalize the chosen class to A=C(01). Three elementary observations
will be used.

* The four adjacent classes disjoint from A in tricoloured corners are
  B=C(234), C=C(23), E=C(24), F=C(34). No opposite variety is disjoint
  from A. Four A and four copies of any one of these classes form an
  opposite target, by using four arcs in each direction between
  {0,1} and a suitable two-element subset of {2,3,4}.
* The reverse cut B has six arcs grouped into three pairs q→{0,1},
  q∈{2,3,4}. A B source sees all three pairs, while C,E,F each miss
  one pair. Thus at least six sources from B,C,E,F, with each of
  C,E,F occurring at most three times, match all six arcs of B.
  Hall is immediate: a set of arcs confined to one pair has at
  least three neighbours; a set meeting two pairs sees every source.
* Each intersection of another class with A has size0,1,2,4, or6.
  An intersection of size1 determines a unique adjacent class.
  Indeed, for an outset S the intersection has size
  |S∩{0,1}|·|{2,3,4}\S|, which is one precisely when S consists
  of one of0,1 and two of2,3,4. Opposite sources have intersection
  size2 or4.

First suppose A occurs at least eight times. Reserve two copies with
the same repeated colour for the bicoloured corners and six further
copies for the tricoloured corners. If A occurs seven times and some
outside source shares a tricoloured corner with A, reserve a same-repeat
pair, use five A and that source for the six tricoloured corners.
Otherwise all seven outside sources lie in B,C,E,F. If one of those
classes occurs four times, the first observation solves. If not, the
second observation supplies the six tricoloured corners of B; two A
copies with the same repeat supply B's bicoloured corners. Hence no
failure has a class of size at least seven.

It remains to consider exactly six A copies. Reserve a same-repeat
pair. If two outside sources can be matched to two distinct A corners,
the four remaining A copies complete the target. Suppose this is not
possible. Let z be the number of outside sources disjoint from A.
Each of their four classes has at most three copies, or the first
observation solves. If z≥6, the second observation solves using two
A for the bicoloured corners of B.

Thus z≤5. At least three of the eight outside sources meet A. Since
they cannot match two distinct A corners, they all meet A in the
same single corner. By symmetry that corner is13, and all these
sources belong to D=C(124). Write m=8−z for their number. The
previous paragraph excludes m≥7, so 3≤m≤6.

The intersections of B,C,E,F with D are respectively

    B: {20,40}; C: {20}; E: {20,23,40,43}; F: {40}.

All are nonempty and avoid13, the corner supplied by A.

* **m=6.** Reserve a same-repeat D pair. Four remaining D, one A
  for13, and any disjoint-from-A source for a different D corner
  fill its six tricoloured corners.
* **m=5.** If two of the three disjoint sources match different D
  corners, use those two, one A for13, and three D for the remaining
  corners, after reserving a D pair. This fails only if all three
  disjoint sources are C, or all three are F. In the C case assemble
  the opposite target ±{02,03,12,13}: four A supply02,03,12,13;
  one D supplies20; and three C supply21,30,31. The F case is
  symmetric, using ±{03,04,13,14}.
* **m=4.** If at least three of the four disjoint sources are E,
  reserve a D pair; the other two D, one A for13, and three E for
  three of20,23,40,43 complete the D target. Otherwise at most
  two are E. Three of the disjoint sources can then match21,30,31:
  the first corner sees B,C,E; the last two see B,C,F; the latter
  pool has at least two copies, the former at least one, and the
  union has four. Together with four A and one D for20, this
  assembles ±{02,03,12,13}.
* **m=3.** There are five disjoint sources and each class count is
  at most three. The same two pools have respectively at least
  two and two sources, so three sources match21,30,31. Four A
  and one D again complete the same opposite target.

Every case gives an assembly, proving the lemma.




# Argument 14: Four identical opposite copies {#arg-14}

Status: a hand proof, using the six-in-one-adjacent-class lemma proved in
[Argument 13](#arg-13). The short shared-four-corners lemma is recalled below. This does not
classify failures with at most three copies of every opposite variety.

## Directed-corner notation {.unnumbered}

Colours are 0,1,2,3,4. Write `ab` for the directed tricoloured corner a→b.
An adjacent class is a cut C(S)={ab:a∈S,b∉S}, with |S|=2 or3. Its pole pair
is the two-element side P of the cut. There are three actual varieties in
this class, indexed by their repeated colour r∉P; their two additional
corners are (r,r,p), p∈P. Two copies having the same repeated colour can
therefore supply both bicoloured corners of that target class.

An opposite variety has eight tricoloured corners: both directions of a
K₂,₂ on four colours, omitting the repeated colour. Normalize an opposite
variety to O=±{13,14,23,24}, where ± adds reversed arcs.

We use the established fact that a fourteen-cube failure has at most five
copies in any adjacent class. Two adjacent classes sharing four tricoloured
corners have at most seven copies in total: if their total were at least
eight, choose a class with at least four copies, reserve two with the same
repeat for its bicoloured corners, use two remaining copies of that class
for its two private tricoloured corners, and fill the four common corners
from the remaining four copies of the two classes. If the other class has
fewer than four copies, the same assignment still works because all
remaining copies have all four common corners. (The six-in-one-class lemma
already handles the case of six or more copies.)

## Hall's cover form {.unnumbered}

If a target with eight corner types cannot be assembled from fourteen
sources, Hall's theorem gives a subset C of its corners, |C|=c≤7, such that
at least 7+c sources have all their target-compatible corners contained
in C. If the target variety itself occurs m times, these m copies do not
belong to that group, so c≤7−m.

Every five-colour source has at least two corners of an opposite target;
its intersection with that target has size 2,4, or8. This follows directly
from the directed cut/biclique descriptions.

## Five identical opposite copies suffice in a fourteen-pool {.unnumbered}

Suppose m≥5 copies of O occur in a failure. The Hall cover has c≤2, so c=2
and m=5. All nine other sources have their O-intersections contained in
this pair. Up to symmetry there are three nonempty possibilities:

1. A row or column pair, e.g. {13,14}: only the adjacent class C(01)
   is eligible, contradicting its bound five.
2. Two oppositely directed arcs on disjoint edges, e.g. {13,42}: two
   adjacent classes sharing four corners are eligible, contradicting
   their combined bound seven.
3. A reversed pair, e.g. {13,31}: precisely two other opposite varieties
   are eligible. Denote them U=±{01,04,13,34} and V=±{02,03,12,13}.
   If one occurs at least eight times it is itself an assembly; otherwise
   both occur at least twice. Four O, two U, and two V build
   T=±{12,14,23,34}: O supplies 14,41,23,32; U supplies 34,43; V supplies
   12,21.

Thus every opposite variety occurs at most four times in a failure.

## The four-copy theorem {.unnumbered}

**Theorem.** If a fourteen-cube failure contains four identical opposite
copies, its coarse profile is precisely O=4 and adjacent-class counts 5,5.
The two adjacent cuts share exactly one tricoloured corner.

Normalize the four copies to O. Hall gives c≤3. Covers with c≤2 are
impossible: the three eligible families above have capacities at most
5,7,8 respectively, whereas c=2 requires nine eligible sources. Thus
c=3, and all ten remaining sources have O-intersection contained in C.

There are five three-corner patterns up to the symmetries of O. Their
complete source lists are as follows. A cut is written by its source side.

| C | Eligible adjacent cuts | Eligible opposite varieties |
|---|---|---|
| 13,14,23 | 01; 124 | none |
| 13,14,31 | 01 | U,V |
| 13,14,32 | 01; 13; 013 | none |
| 13,24,31 | 023; 23 | U,V |
| 13,24,32 | none | none |

The five patterns account for 8,16,16,8,8 of the 56 three-subsets,
respectively. This small geometric table can also be checked without
enumerating subsets: first distinguish whether C contains a reversed arc
pair, then whether its remaining arcs share an endpoint.

### First row {.unnumbered}

There are only two eligible adjacent classes. Each has capacity five, so
their counts are 5,5. They share only the corner 13. This is the asserted
configuration.

### Second row {.unnumbered}

Let g,u,v be the counts of C(01),U,V. The bounds g≤5 and u,v≤4,
together with g+u+v=10, force both u,v positive and at least one of them
at least two. If u≥2, assemble T=±{12,14,23,34} using four O for
14,41,23,32; two U for 34,43; one V for 21; and one C(01) for 12.
If v≥2, instead use target T'=±{03,04,23,24}: four O supply
23,32,24,42; two V supply 03,30; one U supplies 40; and C(01) supplies
04. Both are assemblies, a contradiction.

### Third row {.unnumbered}

Let X=C(01), Y=C(13), Z=C(013), with counts x,y,z. The pairs X,Z and
Y,Z share four corners, so x+z,y+z≤7. Since x+y+z=10, x,y≥3.
At least one count is at least four and hence that class contains two
copies of one repeated variety. Reserve those two for its bicoloured
corners; the six tricoloured corners can be filled as follows.

* If x=5, three X supply 02,03,04, one Y supplies 12, and two O supply
  13,14. If x=4, then z≥1: two X supply 02,03 and one Z supplies 04;
  the other assignments are the same.
* If y=5, three Y supply 10,30,34, one X supplies 12, and two O supply
  32,14. If y=4, then z≥1: two Y supply 10,30 and one Z supplies 34;
  the other assignments are the same.
* Otherwise z≥4, and the bounds force (x,y,z)=(3,3,4). Three X supply
  02,04,12, one Y supplies 34, and two O supply 32,14.

Each assignment uses distinct physical cubes and yields an assembly.

### Fourth row {.unnumbered}

Let X=C(023), Y=C(23), with counts a,b, and let u,v count U,V.
We have a,b≤5, a+b≤7, u,v≤4, and a+b+u+v=10, hence u+v≥3.

If u,v are both positive, use four O for 14,41,23,32, one U for 43,
one V for 12, and any two adjacent copies for 21,34. Both X and Y have
both of these last corners. There are at least two adjacent copies
because u+v≤8. This assembles T=±{12,14,23,34}.

Otherwise, by symmetry take v=0 and 3≤u≤4. Build target U. Three U
copies supply 10,40,43; two further copies from U∪X supply 01,04;
one remaining adjacent copy supplies 34; two O supply 13,31. These
choices are possible because u+a=10−b≥5 and a+b=10−u≥6.

### Fifth row {.unnumbered}

There is no eligible source, so the row is impossible.

This proves the coarse-profile theorem.



# Argument 15: Elementary proofs for the two six-cut support families {#arg-15}

The support-poset statement concerns arbitrary adjacent cuts. The butterfly
profile statement concerns fourteen adjacent cubes with class cap three. It is a conditional
classification by **support family**, not a proof that every fourteen-cube
failure lies in one of these families. In particular, it does not yet rule out
a failure whose tricoloured-corner union supports an opposite-repeat target.

Use colours `0,1,2,3,4`. An adjacent class is a directed complete cut
`S -> S^c`, with `|S|=2` or `3`. Its poles are its two-element side, and the
three varieties in the class are distinguished by their repeated colour,
which is not a pole. A variety with poles `{p,q}` and repeated colour `r`
has bichromatic corners `(r,r,p)` and `(r,r,q)`.

A target cut is **robust** if its six tricoloured corners can still be
matched after any two source cubes are removed. Thus any two distinct
cubes supplying its two bichromatic corners complete a solution.

A robust triple in a failure must use each of its three allowed repeats
once. If another source has pole pair Q meeting its pole pair P in one
colour, that source must repeat the colour in $P\setminus Q$. Otherwise
it shares an allowed repeat with a member of the triple, and the two
sources fill the robust target's bicoloured positions.

## 0. Why there are only two support families {.unnumbered}

This reduction is also elementary; the enumeration of 4,231 labelled
posets is unnecessary.

For a collection of directed cuts, put `a <= b` when the arc `a -> b`
is absent from their union. Equivalently every source outset containing
`a` contains `b`. Including reflexive pairs makes this a preorder.
Break any equivalence class into a linear order. The resulting partial
order is weaker, so all source outsets remain upsets; its incomparability
graph is unchanged. An opposite-repeat target is corner-supported
exactly when this incomparability graph contains a four-cycle (not
necessarily induced).

Consider a partial order on five points whose incomparability graph
has no four-cycle. It contains, as a weaker order, one of these three:

* two points below two other points (`K_{2,2}`), with the fifth isolated;
* a diamond `x<y,z<w`, with the fifth isolated;
* a chain `x<y<z` together with `x<u` and `v<z`.

Here is a short completeness proof. If the height is at least four,
a four-chain contains the first order. If the height is three, choose
`x<y<z`, with remaining points `u,v`. Suppose neither the first order
nor a diamond occurs. Neither `u` nor `v` is comparable with `y`, since
such a comparison gives two points below two others. Each can be above
`x` or below `z`, but not both, which would give a diamond. Avoiding
an incomparability four-cycle between `{x,y}` and `{u,v}` forces one
of `u,v` above `x`; avoiding one between `{y,z}` and `{u,v}` forces
one below `z`. They are different, giving the third order.

If the height is at most two, split the points into nonisolated minima,
nonisolated maxima, and isolated points. An antichain has size at most
three, so these class sizes are `(2,2,1)`, `(2,3,0)`, or `(3,2,0)`.
In the first case every minimum must be below every maximum: a missing
comparison `a<z`, together with the other minimum and the isolated
point, gives an incomparability four-cycle. In the `(2,3,0)` case each
minimum has at least two upper neighbours; otherwise it and the third
maximum are incomparable with the other two maxima. Two different
two-element upper neighbourhoods also give an incomparability
four-cycle. Thus the minima have two common upper neighbours, giving
the first order. The last case is dual.

The size-two and size-three upsets of the first order are exactly the
six butterfly cuts of Section 2. For a diamond, every such upset
contains its top and omits its bottom; conversely every size-two or
size-three subset with these properties is an upset. The same is true
for the third order: containing `x` would require four points, and
omitting `z` would leave at most one. Thus both of the latter orders
give exactly the six common-corner cuts of Section 1.

Consequently every all-adjacent collection whose corner union supports
no opposite-repeat target lies in one of the two support families below.

## 1. The common-corner support {.unnumbered}

For colours $a,b,i,j,k$, the six cuts containing $a\to b$ are
$C(ai),C(aj),C(ak),C(aij),C(aik),C(ajk)$.
Only this support description is needed from the common-corner alternative
here; its numerical assembly lemmas are proved separately.

## 2. Butterfly family: the coarse profile is forced {.unnumbered}

Use pivot colour `0`, and partition the other four colours into
`P={1,2}` and `Q={3,4}`. Assume every class has at most three copies. The six cuts are

    C_1: {0,1} -> {2,3,4},   C_2: {0,2} -> {1,3,4},
    C_3: {1,2,4} -> {0,3},   C_4: {1,2,3} -> {0,4},
    U:   {1,2} -> {0,3,4},   V:   {0,1,2} -> {3,4}.

Their counts are `x_1,x_2,x_3,x_4,u,v`. Define

    L = x_1+x_2+v,       R = x_3+x_4+u,       L+R=14.

The pole pair of `C_i` is `{0,i}`. Those of `U,V` are `P,Q`.
Each block contains three classes of capacity three. Thus $L,R\ge5$.

### Two completion criteria {.unnumbered}

**Low cuts are robust.** For U, the arcs $10,20$ have the common
source pool $C_3\cup C_4\cup U$, of size $R\ge5$. Each other arc's
pool omits at most two high classes and therefore has at least eight
sources. After any two reservations, a set confined to $10,20$ has
at least three neighbours, while a set meeting any other arc has at
least six. Hall proves robustness of U; the argument for V is symmetric.

**High cuts have a completion when their block weight is at least six.**
For C_1, after the two bicoloured reservations suppose at least two
C_1 copies remain. Use two for its private arcs $02,12$. The four
remaining arcs have pools

    03,04: C_1,C_2,V;
    13:    C_1,C_3,U,V;
    14:    C_1,C_4,U,V.

The first pool has size L; each singleton pool has at least
$14-3-3=8$ sources. Removing the four reserved copies leaves at
least two neighbours for a subset of $03,04$ when $L\ge6$,
and at least four for any subset meeting $13$ or $14$. Hall
completes the four positions. The other high cuts are symmetric.

### The low cuts are robust {.unnumbered}

Each block contains three classes of capacity three. Since $L+R=14$,
both block weights are at least five. The low-cut completion criterion
therefore makes both low cuts robust. In a failure, each uses every
repeated colour at most once.

### Both block weights are at least six {.unnumbered}

Suppose $L=5$. Then $R=9$, so $x_3=x_4=u=3$.
The robust low class U uses repeats $0,3,4$. Its repeat-restoration
constraint forces every C_1 source to repeat 2 and every C_2 source to
repeat 1. The high cuts C_3,C_4 have safe completion by their block
weight nine and the displayed high-cut criterion.
No repeated colour can occur in both `C_3,C_4`, nor in one of them
and a positive `C_1` or `C_2`: the two corresponding cubes would
supply a high target's bichromatic corners, leaving two private copies.

If one of `x_1,x_2` is at least two, any repeat `4` in `C_3` or repeat
`3` in `C_4` gives a solution in that positive high class. Reserve
that copy and the corresponding copy of `U` for the bichromatic corners;
use two copies of the chosen high class for its private arcs; use
two of the remaining `L-2=3` sources in `C_1,C_2,V` for `0->3,0->4`;
and use the two remaining `U` copies for its other two arcs.
Avoiding this forces `C_3,C_4` to use only repeats `1,2`; their repeat
sets are disjoint and nonempty, so one uses only `1` and the other only
`2`. Either positive class on the other side then shares a repeat with
one of them and gives a solution.

The only remaining possibility is `x_1=x_2=1,v=3`. Now `V` has repeats
`0,1,2`; its repeat-`1` copy and the `C_2` copy provide the bichromatic
corners of the `C_3` target with repeat `1`, which has safe completion.
Thus `L=5` is impossible, and symmetrically so is `R=5`.

We have proved `L,R>=6`. Every high target
therefore has safe completion whenever two copies remain for its
private arcs.

### Repeated-colour counting forces the profile {.unnumbered}

If a nonpivot colour `q` occurs as a repeat in `U`, robustness of `U`
forbids that repeat in `C_1,C_2`. Also `x_1+x_2=L-v>=3`, so one of
these high classes has at least two copies. Any high-class copy
repeating `q` could pair with the `U` copy to provide that target's
bichromatic corners, with safe completion. Therefore `q` is absent
from **all** high classes. Symmetrically, any nonpivot repeat in `V`
is absent from all high classes.

Furthermore a repeated colour used by a high class of size three
cannot occur in another high class: one copy from each would supply
the size-three class's bichromatic corners, leaving two private copies.

Let `k` be the number of colours still available as high-class repeats.
If `1<=k<=3`, the total `H=x_1+x_2+x_3+x_4` is at most `k+7`.
Indeed, if `t` high classes have size three, they use disjoint nonempty
repeat sets, so `t<=k`. If `t<=k-1`, then `H<=3t+2(4-t)<=k+7`.
If `t=k`, every other high class is empty, so `H=3k<=k+7`.
If `k=0`, then `H=0`.

Suppose one low class has at least two copies. If both low classes
are nonempty, their distinct repeats exclude at least `u+v-2`
nonpivot colours, so `k<=6-u-v<=3`. The bound gives

    H <= 13-u-v < 14-u-v = H,

a contradiction (and `k=0` is immediate). If one low class is empty,
say `v=0,u>=2`, then `k<=5-u<=3`, giving the even stronger
`H<=12-u<14-u`. Thus `u,v<=1`.

Finally `H<=12` and total fourteen force

    (x_1,x_2,x_3,x_4,u,v) = (3,3,3,3,1,1).

**Butterfly profile lemma.** A failing fourteen-pool in this family,
with every class of multiplicity at most three, has profile
$3,3,3,3,1,1$. No repeated-colour enumeration is needed for this statement.



# Argument 16: Three identical opposite cubes plus the reverse six-cut family {#arg-16}

## Statement {.unnumbered}

Let `O` be the opposite-repeat variety with repeated colour `0` and
opposite-pair partition `{1,2}|{3,4}`. A collection consisting of three
copies of `O` and eleven adjacent-repeat cubes from root classes
`0,3,10,12,15,17` always solves.

These six adjacent classes are exactly the directed cuts containing
the common arc `1 -> 2`. Write them as follows, with counts `a,b,c,d,e,f`:

| Name | Outset | Poles | Root class |
| --- | --- | --- | --- |
| `A_0` | `{0,1}` | `{0,1}` | 0 |
| `A_3` | `{1,3}` | `{1,3}` | 10 |
| `A_4` | `{1,4}` | `{1,4}` | 12 |
| `B_0` | `{1,3,4}` | `{0,2}` | 3 |
| `B_3` | `{0,1,4}` | `{2,3}` | 15 |
| `B_4` | `{0,1,3}` | `{2,4}` | 17 |

We may assume every adjacent class count is at most five, by the
established six-class lemma. No shared-four pair bound is needed below.

## 1. An opposite-target construction forces two zero classes {.unnumbered}

Consider the opposite target with repeated colour `1` and partition
`{0,2}|{3,4}` (root target 63). Four of its arcs are
`0->3,0->4,3->0,4->0`.

The first pair can be matched from `A_0,B_3,B_4` precisely when

    a+e >= 1,   a+f >= 1,   a+e+f >= 2.             (1)

The second pair can be matched from the disjoint class set
`B_0,A_3,A_4` precisely when

    d+b >= 1,   d+c >= 1,   d+b+c >= 2.             (2)

If both pairs can be matched, reserve these four adjacent cubes.
Every adjacent class except `A_0` supplies at least one of the four
remaining target arcs `2->3,2->4,3->2,4->2`. Since `a<=5`, there
are at least six non-`A_0` cubes; at least two remain after the four
reservations. Use one for any such arc, and use the three copies of
`O` for the other three arcs. This gives a solution.

Hence one of the two blocks fails its two-corner matching. The symmetry
interchanging colours `1,2` and reversing all arrows swaps the blocks,
so suppose (1) fails. Thus

    a+e+f <= 1,   or   a=e=0,   or   a=f=0.         (3)

The first possibility is impossible in a failure. It would give
`b+c+d>=10`, so one of `b,c,d` is at least four. Any such class is
robust in this situation, as the inequalities in the next section
show, and a robust class of size at least four supplies a solution.

Swapping colours `3,4` interchanges the last two possibilities in (3).
We may therefore assume

    a=e=0.                                        (4)

## 2. Robustness leaves just one count pattern {.unnumbered}

A cut is robust if its six tricoloured corners survive arbitrary
removal of two source cubes. The three copies of `O` are included
in these matching counts. The following are the nonautomatic Hall
conditions for the four classes needed here:

| Class | Conditions for robustness |
| --- | --- |
| `A_3` | `b+d>=3`, `b+f>=3`, `b+c+d>=4`, `b+d+f>=4`, `b+c+d+f>=5` |
| `A_4` | `c+d>=3`, `c+e>=3`, `b+c+d>=4`, `c+d+e>=4`, `b+c+d+e>=5` |
| `B_0` | `b+d>=3`, `c+d>=3`, `b+c+d>=5` |
| `B_4` | `a+f>=3`, `b+f>=3`, `a+b+f>=4`, `a+e+f>=4`, `a+b+e+f>=5` |

These are obtained directly from the six arcs of the indicated cut:
any tested subset meeting `O` has three additional neighbours. The
total-count condition is automatic because there are eleven adjacent
sources. The table also justifies the preceding paragraph when
`a+e+f<=1`.

Under (4), put `Y=b+c+d=11-f>=6`. Any one of `b,c,d` of size at least
four satisfies its row of the table and gives a solution. Thus each
is at most three. If `f=5`, its class is robust. If `f=4`, its class
is robust unless `b=0`, but then `c+d=7` contradicts `c,d<=3`.
Therefore `f<=3` as well.

The four counts `b,c,d,f` sum to eleven and are at most three. Exactly
one equals two and the other three equal three.

## 3. Three placements of the two are impossible by repeat constraints {.unnumbered}

A robust class of size three in a failure has one copy of each of
its three varieties. If a source's pole pair meets the robust pole
pair in one colour, its repeated colour is forced to be the unmatched
pole of the robust class; otherwise the two corresponding copies
provide that robust target's two bichromatic corners.

If `d=2` or `f=2`, both `A_3,A_4` have size three and are robust.
Their pole pairs `{1,3}` and `{1,4}` meet. One robust class therefore
forces the other to repeat a single colour, contradicting its three
distinct repeats.

If `b=2`, the classes `A_4,B_0` are robust of size three, with disjoint
pole pairs `{1,4}` and `{0,2}`. Every `B_4` copy, with poles `{2,4}`,
would have to repeat `1` because of `A_4`, and repeat `0` because of
`B_0`. This is impossible.

It remains that

    (b,c,d,f) = (3,2,3,3).

## 4. The final forced case has an explicit eight-cube solution {.unnumbered}

Now `A_3,B_0` are robust of size three. Their repeats are respectively
`{0,2,4}` and `{1,3,4}`. The pole-intersection rule forces both `A_4`
copies to repeat `3`, and all three `B_4` copies to repeat `0`.

Build an adjacent target of class `A_4` with repeated colour `0`:

| Target corner | Source |
| --- | --- |
| bichromatic `(0,0,1)` | the repeat-`0` copy of `A_3` |
| bichromatic `(0,0,4)` | one `B_4` copy |
| `1 -> 0` | another `A_3` copy |
| `1 -> 2`, `4 -> 0`, `4 -> 2` | the three `B_0` copies |
| `1 -> 3`, `4 -> 3` | the two `A_4` copies |

This uses eight distinct adjacent cubes; none of the three opposite
cubes is needed in the final construction. Every possible case has
therefore yielded a solution.




# Argument 17: Butterfly repeats and concentrated-opposite tools {#arg-17}

## 1. Notation {.unnumbered}

Let the colours be V={0,1,2,3,4}. Write `ab` for the directed tricoloured corner
a→b and β(r,p) for a bichromatic corner whose repeated colour is r and whose
singleton colour is p. An adjacent class is the directed cut
δ⁺(S)={ab:a∈S,b∉S}, where |S|=2 or 3. Its pole pair is the two-element side,
and it has three physical varieties, according to the repeated colour outside
the pole pair. A variety with poles {p,q} and repeated r has bichromatic corners
β(r,p),β(r,q). Write O(r;P|Q) for the opposite-repeat variety whose eight corners
are the two directions of the four edges between P and Q.

A target is constructible precisely when its eight corner positions can be
assigned injectively to available cubes possessing those corners. All
constructions below explicitly give such assignments or use elementary
matching in small disjoint pools.

## 2. A concentrated-opposite extension {.unnumbered}

Write $O=O(0;12\mid34)$, $A=C(01)$, and $B=C(124)$.

### A useful extension lemma {.unnumbered}

**Lemma.** Three O, five A, five B, and any additional variety Y≠O are soluble.

The four A-private corners are P_A={02,03,04,12}; the four B-private corners are
P_B={10,20,40,43}. Every Y≠O contains a corner in P_A∪P_B. For an adjacent cut
avoiding P_A, membership of 0 in its outgoing side would force membership of
2,3,4, which is impossible. With 0 excluded, avoiding P_B excludes 1,2,4 too,
leaving an outgoing side of size at most one. For an opposite variety, avoiding
the union requires omitting vertex 0 because every edge incident to 0 occurs
in the union in some direction. The omitted vertex is therefore 0; avoiding
edges12 and34 then forces precisely O.

If Y meets P_A, choose two same-repeat A cubes for the two bichromatic corners
of their A target; such a pair exists among five A cubes and three repeated
colours. The remaining three A cubes cover the other three A-private corners,
Y covers the selected one, and two O cubes cover 13,14. The B case is identical.

## 3. The pure-adjacent family: nine derangements {.unnumbered}

Partition V=P⊔{z}⊔Q, where |P|=|Q|=2. Include one cube from each low class

    L_P=δ⁺(P),  L_Q=δ⁺(P∪{z}),

and three cubes from each of the four high classes C_v, v≠z, where

    C_v=δ⁺({z,v})         if v∈P,
    C_v=δ⁺(V\{z,v})      if v∈Q.

Every high class has pole pair {z,v}.

**Proposition.** If the collection fails, both low cubes repeat z,
and there is a derangement π of V\{z} such that all three cubes in C_v repeat
π(v).

For necessity, fix v∈P, write P={v,w}, Q={q_1,q_2}, and consider a C_v target.
Its private tricoloured corners zw,vw require two C_v copies. Its other four
tricoloured corners are zq_1,zq_2,vq_1,vq_2. The disjoint pools C_w∪L_Q,
C_{q_1},C_{q_2} have respectively four, three, three copies and can supply
respectively the first two, third, fourth of these corners. Reserving any two
cubes for bichromatic corners leaves at least two, one, one in those pools,
so they still complete the target. The dual argument applies to v∈Q.

If repeated colour r occurs in two different high classes C_v,C_u, use C_v
for β(r,v), C_u for β(r,z), two remaining C_v for its private tricoloured
corners, and the pool construction for the rest. Thus each nonpivot colour
can occur in at most one high class in a failure. Four nonempty high classes
use four nonpivot colours, so each class uses exactly one repeated colour and
these colours are distinct. The own pole colour v cannot be repeated in C_v;
hence the resulting permutation is a derangement.

If L_P repeats r∈Q, choose v∈P and use L_P for β(r,v), the unique high class
repeating r for β(r,z), two C_v for the private tricoloured corners, and the
same pool completion. Therefore L_P repeats z. By duality L_Q repeats z too.

## 5. Opposite-triangle extension lemmas {.unnumbered}

Use the following three opposite types:

    X=O(0;12|34) [60],
    Y=O(2;03|14) [67],
    Z=O(4;01|23) [72].

They share precisely the bidirected edge13 pairwise.

**Lemma A.** Three X, two Y, two Z, and any eighth cube T are soluble.

For the target O(0;13|24) [61], two Y fill34,43; two Z fill12,21;
three X can fill any three of H_1={14,41,23,32}. Thus this target works if T
has any corner in H_1. The target O(0;14|23) [62] gives the same assignment
with H_2={13,31,24,42}. The sets H_1,H_2 partition the eight corners of X,
and every variety shares at least two corners with X, proving the claim.

**Lemma B.** Three X, three Y, one Z, and an eighth cube T are soluble unless
T is X or Y.

The following three targets work whenever T supplies one of the indicated
two holes. For the other hole, interchange the two directions in the final
column. Entries are the corners assigned to each source pool.

| Target | Three X | Three Y | One Z | Hole supplied by T |
|---|---|---|---|---|
| O(0;14\|23) [62] |13,42,24|43,31,34|21|12 (or21)|
| O(2;01\|34) [66] |41,31,14|13,40,04|30|03 (or30)|
| O(4;03\|12) [74] |32,31,23|13,10,01|20|02 (or20)|

The six possible holes form the two directions of the path1–2–0–3. Every
adjacent cut crosses this path: avoiding it would put all four path vertices
on the same side, impossible for a two-three cut. An opposite variety
avoiding the path cannot omit the isolated colour4, because the four
remaining vertices would have to lie in one side of its two-two partition.
Nor can it omit a path endpoint, because the other three path vertices
would then have to lie in one side. Omitting the internal vertex0 forces X;
omitting the internal vertex2 forces Y. These are the only exceptions.

## 6. Three-anchor Hall covers of size at most three {.unnumbered}

Suppose a fourteen-cube failure contains three copies of X [60]. Assuming
the proved caps (each adjacent class≤5, each shared-four pair≤7, each
opposite variety≤3 unless the four-anchor branch applies), a Hall obstruction
for target X gives a cover of at most four of its corners. For size c, at
least 7+c nonanchor cubes have their entire intersection with X in the
cover. Covers of size two are impossible by the caps. The five size-three
cover orbits have representatives below, using X corner order
13,14,23,24,31,32,41,42. Class labels are outgoing sets, not numeric indices.

| Cover | Permitted adjacent classes | Permitted opposite types |
|---|---|---|
|13,14,23|01,124|none|
|13,14,31|01|Y,Z|
|14,23,31|none|none|
|13,24,31|023,23|Y,Z|
|14,24,31|123,023,23|none|

The first row forces five copies in each class and one outside cube T≠X,
so the extension lemma of Section2 applies. The second row forces at least
two each of Y,Z, so Lemma A applies. The third is empty.

For the fourth row write u,v for the two class counts and p,q for Y,Z.
If u+v≥6 and one of u,v≥4, choose a repeated-colour pair in the larger
class for its two bichromatic corners. Two more cubes from that class
cover its two private tricoloured corners (01,04 for023, or20,30 for23).
The other class supplies21,34, using a fifth cube in the larger class if
necessary, while two X supply24,31. Hence failure requires u+v≤5 or
u=v=3. Since u+v+p+q≥10 and p,q≤3, the first alternative gives p,q≥2,
so Lemma A applies. In the second alternative p+q≥4. Again Lemma A
applies unless {p,q}={3,1}. This final case has exactly ten cubes in the
cover and one cube T outside, and Lemma B applies because T is neither X
nor the opposite type of multiplicity three.

For the fifth row an equivalent normal form is classes U=01, V=13,
W=013, with counts u,v,w. We have u+v+w≥10, u+w≤7, v+w≤7, each≤5,
so u,v≥3 and at least one class has count≥4. Reserve two same-repeat
cubes in such a class for the two bichromatic positions. The following
tricoloured completions use only two X:

| Case/target | Remaining U | Remaining V | Remaining W | X |
|---|---|---|---|---|
|u=5, U|02,03,04|12|—|13,14|
|u=4, U|02,03|12|04|13,14|
|v=5, V|12|10,30,34|—|32,14|
|v=4, V|12|10,30|34|32,14|
|w≥4, W|02,04,12|34|—|32,14|

In the last row the caps force w=4,u=v=3. Thus every size-three cover is
eliminated. Thus a failing collection with three identical opposite cubes
must have a size-four Hall cover. The arguments above do not use the
subsequent analysis of those four-corner covers.




# Argument 18: Hand elimination of three-anchor cover orbit27 {#arg-18}

Use three copies of X=O(0;12|34). The allowed adjacent classes and counts are

    A=01 (a), B=123 (b), C=023 (c), D=23 (d),

and the other opposite types are Y=O(2;03|14) [67] and Z=O(4;01|23) [72],
with counts p,q. Thus

    a+b+c+d+p+q=11,
    a,b,c,d≤5,  p,q≤3,  b+d≤7,  c+d≤7.

The opposite-triangle extension lemmas give p+q≤3 in a failure. If both
counts are at least two, the 3X+2Y+2Z core plus any extra cube solves. If one
count is three and the other positive, the 3,3,1 core plus a cube different
from its two large types solves; such an extra cube exists by the caps and
the fourteen-cube total. Consequently at least eight adjacent cubes remain.

## 1. A four-position Hall reduction {.unnumbered}

Consider target T=O(3;04|12) [71]. Corners41,42 are supplied only by X among
the allowed groups, so reserve two X for them. The third X can fill14 or24.
Every adjacent cube also fits14 or24, and at least eight adjacent cubes
exist. Therefore it suffices to match the four positions

    Q={01,02,10,20}

to distinct nonanchor cubes. Once this is done, an unused adjacent cube
and the third X fill14,24. The intersections with Q are:

| Source | Available positions |
|---|---|
|A|02|
|B|10,20|
|C|01|
|D|20|
|Y|01,10|
|Z|02,20|

Every three-position subset has at least six neighbours (it excludes at
most one adjacent class of count≤5), and all four have eleven neighbours.
Among the six pairs, four are automatically safe: their neighbour counts
are a+c+p+q=11-b-d≥4; a+b+p+q=11-c-d≥4;
b+c+d+p+q=11-a≥6; and a+b+d+q=11-c-p≥3.
The other two pairs have neighbour counts b+c+p and b+d+p+q.

Thus if T cannot be assembled, at least one of the following conditions holds:

1. c=p=0 (position01 missing);
2. a=q=0 (position02 missing);
3. b=p=0 (position10 missing);
4. b=d=q=0 (position20 missing);
5. b=c=0,p=1 (01 and10 have only one common source);
6. b=1,d=p=q=0 (10 and20 have only one common source).

For the last two cases, we have assumed all individual positions supported;
any other pair deficiency is already included among1–4. This is a direct
four-position Hall calculation, with no multiplicity enumeration.

## 2. All cases with a>0 are soluble {.unnumbered}

A useful second target is Z itself. Reserve two X for13,31. Its other six
positions split into L={02,03,12} and R={20,21,30}. A fits all of L; B fits20,30;
C fits21; D fits all of R; Y fits none; and Z fits all six. Hall's condition
for these two blocks is satisfied if

    a+q≥3,
    b+d+q≥2,
    c+d+q≥1,
    a+b+d+q≥5,
    a+c+d+q≥4.                         (*)

The two additional full-block inequalities are automatic: R has
11-a-p≥3 neighbours and all six positions have11-p≥8. The five displayed
inequalities are the strongest requirements for L, {20,30}, {21},
L∪{20,30}, and L∪{21}, respectively; all smaller subsets follow.

Assume a>0. Condition2 of the previous section is impossible.

* In condition1, c=p=0. The pair cap b+d≤7 gives a+q≥4. The total gives
  b+d+q=11-a≥6 and a+d+q=11-b≥6. Also d+q≥1, since otherwise a+b=11 would
  contradict the class caps. All of(*) hold, so Z is assembled.
* In condition3, b=p=0. Now c+d≤7 gives a+q≥4, while a+d+q=11-c≥6 and
  c+d+q=11-a≥6. Thus(*) hold unless d+q≤1. In that exception a+c≥10;
  the caps and total force a=c=5,d+q=1. A same-repeat pair among the five
  A cubes fills an A target's bichromatic positions; the remaining three
  A fill02,03,12, one C fills04, and two X fill13,14.
* In condition4, b=d=q=0 and a+c+p=11. If p≤2, one of a,c is five. Five A
  with any C solve as just described. Five C with any A similarly solve:
  reserve a same-repeat C pair; use C:01,21,34, A:04, X:24,31. If p=3,
  then a,c≥3, and target Y is assembled by Y:10,40,43; X:13,31;
  C:01,34; A:04.
* In condition5, b=c=0,p=1 and a+d+q=10. Since a,d≤5, both a+q and d+q
  are at least five, so every inequality(*) holds.
* In condition6, the total forces a=c=5. The five-A construction above
  applies.

Hence every collection in this cover with a>0 is soluble.

## 3. The cases with a=0 {.unnumbered}

Suppose first that q>0. Conditions2 and4 are impossible. Condition1 would
give b+d+q=11, contradicting b+d≤7 and q≤3. Condition3 gives the same
contradiction with c+d. Condition5 would give d+q=10, contradicting d≤5,
q≤3. Condition6 requires q=0. Therefore the four-position matching succeeds
and T is assembled. A failure must have q=0.

Now a=q=0 and b+c+d+p=11. The pair caps imply

    b+p≥4,  c+p≥4.

If p=2, then b,c≥2. Assemble target Y by Y:40,43; X:13,31; C:01,04;
B:10; and any further B,C,D cube at34. If p=3, then b,c≥1; use
Y:40,43,01; X:13,31; C:04; B:10; and a further adjacent cube at34.
The extra cube exists because at least eight adjacent cubes are available.

It remains p≤1, so b+c+d≥10 and b,c≥3. Some class has count at least four.
Reserve two same-repeat copies in that class for its bichromatic positions;
the following table supplies its six tricoloured positions:

| Case/target | Tricoloured placements |
|---|---|
|b=4, B|B:10,20; D:30; C:34; X:14,24|
|b=5, B|B:10,20,30; C:34; X:14,24|
|c=4, C|C:01,04; D:21; B:34; X:24,31|
|c=5, C|C:01,04,21; B:34; X:24,31|
|d≥4, D|D:21,34; B:20,30; X:24,31|

When b=4 or c=4, the other two counts sum at least six and neither exceeds
five, so d≥1 as required. In the final row at least two D remain after the
reserved pair, and b≥3 supplies the two B. All cases therefore solve.

This closes cover orbit27 using only the established caps, two elementary
Hall calculations on four and six positions, and explicit corner assignments.



# Argument 19: Hand elimination of three-anchor cover orbits 23, 53, and 102 {#arg-19}

Use X=O(0;12|34) three times. All adjacent-class counts are at most five;
each other opposite variety has count at most three. A shared-four adjacent
pair has total at most seven. The missing-pair bound says that the total
number of cubes omitting a fixed bichromatic colour pair is at most seven.

## Mask23 {.unnumbered}

The allowed groups are A=01 (a), B=124 (b), Y=O(2;03|14) (p), and
Z=O(4;01|23) (q), with a+b+p+q=11.

The opposite-triangle extension lemmas show p+q≤3 in a failure. Indeed,
p,q≥2 gives the 3,2,2 core, while one count3 and the other positive gives
the 3,3,1 core plus an additional cube different from its two large types.
Such an additional cube must exist since every opposite count is at most3.

Therefore a+b≥8. If a=5, any Y or Z meets an A-private corner; two same-repeat
A fill the bichromatic positions, three A fill three private corners, Y/Z
fills the fourth, and two X fill13,14. There is necessarily a Y or Z because
a+b≤10. The same argument handles b=5. Thus a=b=4 and p+q=3. If p≥2,
make a B target: reserve two same-repeat B for its bichromatic positions;
the two remaining B and two Y fill its four private corners10,20,40,43
(Y fits10,40,43); two X fill13,23. If q≥2, the symmetric A target works,
because Z fits three of the four A-private corners02,03,04,12. One of p,q
is at least two, completing the proof.

## Mask53 {.unnumbered}

The adjacent classes are A=03 and B=124, with counts a,b. The allowed
opposite types and counts are

    U=O(1;03|24) [64], u;
    Y=O(2;03|14) [67], y;
    Z=O(4;01|23) [72], z;
    V=O(4;02|13) [73], v;
    W=O(4;03|12) [74], w.

All eleven nonanchor cubes lie in these groups. The adjacent varieties with
poles03 and the opposite varieties U,Y,W omit the bichromatic pair03.
Consequently

    a+b+u+y+w≤7,

and hence z+v≥4. Since z,v≤3, both are positive.

If z,v≥2, use three X, two Z, and two V. These seven cubes can fill any seven
corners of target W. To see this, W's corners split into three pairs/blocks:

    P={01,10}, Q={02,20}, R={13,31,23,32}.

Two V cover P, two Z cover Q, and three X cover three corners of R. This
handles a hole in R. If the hole lies in P, the spare V fills23 or32 and X
fills the other three R corners. If it lies in Q, the spare Z fills13 or31
and X fills the other three R corners. Any eighth cube shares a corner
with W, so it fills one of the permissible holes and completes W.

The remaining count pattern is {z,v}={3,1}. The colour permutation (1 2)
exchanges Z,V and U,Y while preserving X,A,B,W, so take z=3,v=1. Three X
fill23,31,32 of W; three Z fill13,02,20; one V fills one of01,10. Any extra
cube having01 or10 fills the other. Every cube of A,B,Y,W has at least one
of those corners. If none of those groups occurs, the remaining seven
nonanchor cubes must all be U, contradicting u≤3. Thus W is constructible.

## Mask102 {.unnumbered}

The adjacent classes are

    A=13 (a), B=024 (b), C=24 (c), D=013 (d),

and the allowed opposite types are

    E=O(0;13|24) [61], e;
    U=O(1;03|24) [64], u;
    V=O(2;04|13) [68], v;
    Y=O(3;01|24) [69], y;
    Z=O(4;02|13) [73], z.

Their counts total eleven. Set F=a+d, R=b+c, K=u+v, L=y+z. The shared-four
bound gives F,R≤7 and the individual opposite bound gives K,L≤6. This
orbit does not require the missing-pair bound.

### Hall's condition for E {.unnumbered}

Every allowed source intersects target E in at least four corners; E itself
intersects it in all eight. Thus a set of at least five target corners has
all fourteen cubes as neighbours. A set of at most three corners meeting
X has its three anchor cubes as neighbours. A set of four corners meeting
X also has a nonanchor neighbour: otherwise all eleven nonanchor cubes
would have exactly the same four-corner intersection with E. The only
groups with identical four-corner intersections are A,D (total F≤7) and
B,C (total R≤7); each of U,V,Y,Z has its own distinct intersection and
count≤3. Hence eleven such cubes cannot exist.

It remains to inspect subsets of

    Q=E\X={12,21,34,43}.

The intersections of the nonanchor groups with Q are:

| Group | Available corners of Q |
|---|---|
|F=A∪D|12,34|
|R=B∪C|21,43|
|K=U∪V|34,43|
|L=Y∪Z|12,21|
|E|all four|

Any pair in Q has at least four neighbouring cubes: a same-row pair omits
only F or R (each at most seven of eleven), a same-column pair omits only
K or L (each at most six), and a diagonal pair meets every group. Any set
of three or four corners meets every group. Consequently the only possible
Hall failure for E is an entirely unsupported single corner of Q:

    F+L+e=0, F+K+e=0, R+L+e=0, or R+K+e=0.

Global arc reversal exchanges F,R; the colour permutation (1 3)(2 4)
exchanges K,L while preserving F,R. We may therefore assume

    F=L=e=0.

Thus only B,C,U,V remain, with b+c+u+v=11. Since b+c≤7, u+v≥4. Since u,v≤3,
both are positive.

### Three explicit completions {.unnumbered}

If u,v≥2, take any B or C cube T, which exists because b+c≥5. Make target
O(1;02|34) [63] with X:24,32,42; U:04,40; V:03,30; T:23.

If u=3,v=1, then b+c=7 and b,c≤5 give b,c≥2. Make the same target63 with
X:24,32,42; U:23,40,04; V:30; B:03.

If u=1,v=3, again b+c=7 gives b,c≥2. Make target O(2;01|34) [66] with
X:41,31,13; U:04; V:14,30,03; C:40.

These cases exhaust u+v≥4 with u,v≤3, proving that mask102 has no failure.

All three orbit proofs use only the stated caps and explicit assignments or
the elementary four-position Hall argument above. No multiplicity search is
needed.



# Argument 20: Hand elimination of three-anchor cover orbits 30 and 51 {#arg-20}

Notation is as in [Argument 17](#arg-17): an adjacent class is named by
its outgoing set; X=O(0;12|34) is available three times. Adjacent counts are
at most five, shared-four pairs have combined count at most seven, and each
other opposite type has count at most three. Corner labels `ab` mean a→b.

## Mask30: four adjacent classes {.unnumbered}

The classes and counts are

    A=02 (a), B=123 (b), C=023 (c), D=23 (d),
    a+b+c+d=11,
    a+c≤7, b+d≤7, c+d≤7.

No other opposite type occurs.

### A class of count at least four gives a target {.unnumbered}

Two cubes repeating the same colour exist in every class of at least four;
reserve them for that class's two bichromatic corners.

For a C target, two X fill24,31; the remaining four tricoloured corners are
01,04,21,34. If c=5, the three remaining C cubes fill three of these and any
other adjacent cube fills a suitable fourth. If c=4, two remaining C fill
two positions. Since b≤5 and a+b+d=7, at least two other cubes lie in A∪D.
Each A fits three of the four positions, and each D fits21,34, so these two
cubes can fill distinct positions; the two C fill the rest. Thus c≥4 solves.
The dual argument gives d≥4: two X fill24,31 and the residual four positions
are20,21,30,34; B fits20,30,34, C fits21,34, and a≤5 guarantees two B∪C cubes
when d=4.

We may therefore suppose c,d≤3. For an A target, two X fill23,24. The other
four positions are01,03,04,21. Position03 requires A, while C fits01,04,21
and D fits21. Consequently a=5 solves whenever c+d≥1; a=4 solves whenever
c≥1 and c+d≥2. The former condition follows from b≤5 and total11. In the
latter case, c+d=1 with c≥1 would force b=6, impossible. The sole exception
is c=0; then b+d=7 with d≤3, so b≥4 and d≥2. For a B target, two X fill14,24
and the remaining four positions10,20,30,34 are filled by the remaining B
and D cubes: b=4 leaves two B and at least two D, while b=5 leaves three B
and at least one D. Thus the exception also solves. Interchanging A,B and
C,D treats b≥4.

### The remaining counts are 3,3,3,2 {.unnumbered}

Every class of count three must use three distinct repeated colours. Indeed,
if a repeated pair occurs, reserve it for the two bichromatic positions and
complete the six tricoloured positions as follows (all class counts are now
at least two):

| Target | Tricoloured placement |
|---|---|
|A|A:03; C:01,04; D:21; X:23,24|
|B|B:10; D:20,30; C:34; X:14,24|
|C|A:01,04; D:21; B:34; X:24,31|
|D|B:20,30; C:21,34; X:24,31|

If c=d=3, both classes contain repeated colour0. Use C_0 and D_0 for the
bichromatic corners β(0,1),β(0,2) of the target with outgoing set12. Its six
tricoloured positions are filled by B:10,14; D:20,24; X:13,23. Two D remain
after reserving D_0.

If c=2 or d=2, then a=b=3. Both classes contain repeated colour1. Use A_1
for β(1,2) and B_1 for β(1,0), making an A target. Its tricoloured positions
are filled by A:03; C:01,04; D:21; X:23,24. Thus every case solves.

## Mask51: a three-leaf star and two opposite types {.unnumbered}

The classes and counts are

    A=01 (a), B=03 (b), C=13 (c), D=013 (d),
    Y=O(2;03|14) (p), Z=O(4;01|23) (q),
    a+b+c+d+p+q=11,
    a+d≤7, b+d≤7, c+d≤7.

The permutation (1 3)(2 4) fixes X,C,D and exchanges A with B and Y with Z.

### Opposite targets reduce the possibilities {.unnumbered}

First, p and q cannot both be positive. The triangle extension lemmas already
exclude p,q≥2, or one count3 and the other positive. The remaining possibilities
have p+q≤3 and at least eight adjacent cubes. Make target O(0;13|24): reserve
X for41,23, Y for43, Z for21. Its remaining positions are12,14,32,34. The third
X can fill14 or32. A fits12,14; B fits32,34; C,D fit all four. Three adjacent
cubes can supply the other three positions unless every adjacent cube lies
in A or every one lies in B. Those exceptions violate the class cap five
because at least eight adjacent cubes are available. More explicitly, if
both A and B occur use one at12 and one at34, and the third at14 or32; if
only one of A,B occurs, a C or D supplies the position on the other side,
and two of the many remaining adjacent cubes complete. If neither occurs,
three C/D cubes work. Thus p,q>0 is impossible.

By symmetry assume q=0. We show that the only possibilities not already
soluble by an opposite target are:

    p=0; or
    p=1, (a=0 or c=0), b≥3; or
    p=2, c=0, a,b≥2.

If p≥1 and a,c≥1, use target O(1;02|34). Three X fill23,24,42; one Y fills40;
one A fills03; one C fills30. The remaining positions04,32 have adjacent
support A∪B∪D and B∪C∪D, respectively. After reserving the A and C cubes,
each of those pools has at least two available cubes: there are at least
eight adjacent cubes altogether and neither a nor c exceeds five. Hence
two distinct remaining cubes fill04,32. Therefore a=0 or c=0.

For p=1 the adjacent total is10. If a=0, the pair caps b+d,c+d≤7 give b,c≥3;
if c=0, a+d,b+d≤7 give a,b≥3. In either case b≥3.

For p=2, suppose c>0. Then a=0, b+c+d=9, and the pair caps give b,c≥2. Make
target Y: two Y fill40,43; two X fill13,31; two B fill01,04; two C fill10,34.
Thus c=0. With a+b+d=9, the pair caps imply a,b≥2.

For p=3, if a,c>0 the earlier target works. If c=0, then a+b+d=8 and the pair
caps give a,b≥1. Make target Y: three Y fill10,40,43; two X fill13,31; the
other three positions01,04,34 are supplied by B and A∪B∪D. There are at least
two cubes in B∪D, since otherwise a≥7; one B fills01, another B/D fills34,
and one further adjacent cube fills04. If instead a=0 and c>0, then b,c≥1.
Two Y fill40,43, two X fill13,31, one B fills01, and one C fills10. The third
Y fills one of04,34, and an additional B/C/D cube fills the other; such a
cube exists because b+c+d=8. Hence p=3 always solves.

### Completion after a repeated pair in a large adjacent class {.unnumbered}

There are at least eight adjacent cubes in all remaining cases. Reserve a
same-repeat pair in a class of count≥4. The following pool descriptions give
the six tricoloured placements:

* A target: two X fill13,14; an A fills03; the three positions02,04,12 remain.
  A fits all three, B fits02,04, C fits12, and D fits all three. For a=5 this
  is always possible. For a=4 it is possible whenever b+d>0: after using one
  further A, the other pools contain at least four cubes, and a B/D plus a
  suitable second cube fills two distinct remaining positions.
* B target: the symmetric statement holds, with the sole potential exception
  b=4,a=d=0.
* C target: two X fill14,32; two remaining C fill10,30. The other positions12,34
  are supported by A∪D and B∪D, respectively. Thus c=4 works when a+d,b+d>0;
  c=5 always works because its third remaining C fills one of12,34.
* D target: two X fill14,32, leaving02,04,12,34. At least two D remain after
  reserving the pair. Every other adjacent class fits at least two of these
  positions; two such cubes can fill distinct positions and the D fill the
  rest. If d=5 only one other cube is needed. Thus d≥4 always works.

For p=0, total11 and the cap5 exclude every exception in this list. For p=1,
the adjacent total10 and either a=0 or c=0 again exclude all exceptions:
when a=0, b,c≥3 and any b=4 or c=4 forces d>0; when c=0, a,b≥3. For p=2,
c=0 and a,b≥2, so again every count≥4 is soluble.

### Collections with all adjacent counts at most three {.unnumbered}

For p=1 there would be only three nonzero adjacent classes, contributing
at most nine cubes, contradicting the adjacent total10. For p=2 the only
remaining profile is a=b=d=3,c=0. For p=0 the four counts are3,3,3,2.

The following useful core handles all cases with a,b≥3 and d≥1: three A,
three B, one D, and two X are always soluble. If a same-repeat pair occurs
among the A cubes, reserve it and use A:03; B:02,04; D:12; X:13,14. A repeated
pair among B is treated symmetrically. Otherwise A and B each use all their
three repeated colours and have a common repeated colour r∈{2,4}. Reserve
A_r for β(r,1) and B_r for β(r,0), making an A target, and use the same six
tricoloured placements. This proves the core assertion.

It remains in the p=0 case that a=2,b=c=d=3, or its symmetric image. In the
first case a repeated pair in B would solve by B:01; A:02,04; D:34; X:31,32;
a repeated pair in D would solve by A:02,04; C:12; B:34; X:14,32. Hence B
and D each use all three permitted repeated colours and both contain colour1.
Use B_1 and D_1 for β(1,3),β(1,4), making the adjacent target with outgoing
set012. Its tricoloured positions are A:03,13; B:04; D:14; X:23,24. All
reserved and assigned cubes are distinct. The symmetric case follows by
(1 3)(2 4).

Thus mask51, like mask30, contains no fourteen-cube failure. No multiplicity
enumeration is used in these proofs; every case follows from the stated
caps, totals, and explicit corner assignments.



# Argument 21: The O3 Hall-cover case 54 {#arg-21}

This note gives a hand proof for one cover case. The eight tiny matching
constructions below were found by computation; the deductions from them are
ordinary integer inequalities and do not use enumeration of count vectors.
Each construction can be checked directly against the directed-corner model.

Use the root model's classes and opposite varieties. Let X=O60 have three
copies. Let A, B, C be adjacent classes 4, 10, 17, with counts a,b,c, and let
U=O64 and V=O73 have counts u,v. Thus

  a+b+c+u+v=11,

with a,b,c<=5, u,v<=3. The standard pair caps give

  a+c<=7, b+c<=7, c+u<=7, b+v<=7.

Specifically, a+c and b+c are bounded by the shared-four adjacent-class
lemma. The bounds c+u<=7 and b+v<=7 are the missing-colour-pair bounds for
the unordered colour pairs {2,4} and {1,3}, respectively, and follow
from the eight-plus-three lemma. These are independent inputs to the
argument.

Geometrically, A is the cut {0,3}->{1,2,4}, B the cut
{1,3}->{0,2,4}, and C the cut {0,1,3}->{2,4}.
The opposite sources X,U,V are the bidirected complete bipartite graphs
12|34, 03|24, and02|13, respectively. Here pq|rs means that every
directed edge between {p,q} and {r,s} is present, in both directions.

The following eight-cube pools have an opposite-repeat assembly regardless
of the repeated-colour labels of A,B,C:

| Core | Target |
| --- | --- |
| 3X+2A+2B+U | O71 |
| 3X+2C+U+2V | O61 |
| 2X+A+2B+C+2V | O73 |
| 3X+B+C+2U+V | O61 |
| 3X+A+B+3U | O74 |
| 3X+3A+U+V | O74 |
| X+A+B+2C+3V | O73 |
| X+2A+3B+2V | O73 |

The target names denote bidirected graphs O71=04|12, O61=13|24,
O73=02|13, O74=03|12. The following arc-to-source assignments verify
the cores in the same order as the table (each arrow consumes one cube):

1. 01:A,02:A,10:B,14:B,20:U,24:X,41:X,42:X.
2. 12:V,14:C,21:V,23:X,32:X,34:C,41:X,43:U.
3. 01:A,03:V,10:B,12:C,21:V,23:X,30:B,32:X.
4. 12:C,14:X,21:V,23:U,32:X,34:B,41:X,43:U.
5. 01:A,02:U,10:B,13:X,20:U,23:U,31:X,32:X.
6. 01:A,02:A,10:V,13:X,20:U,23:X,31:A,32:X.
7. 01:A,03:V,10:V,12:C,21:V,23:X,30:B,32:C.
8. 01:A,03:V,10:B,12:B,21:V,23:X,30:B,32:A.

## 1. A failure has u=0 {.unnumbered}

Suppose u>=1. The first core implies a<=1 or b<=1.

If a<=1, then b+c<=7 and the total give u+v>=3.

* If v>=2, the second core forces c<=1. Since b+v<=7,
  a+c+u>=4, so u>=2. If c=1, then b>=3 and the fourth core
  applies. If c=0, then a+u>=4 forces a=1,u=3, and the fifth
  core applies (b>=4).
* If v=1, then u>=2. The total forces b,c>=1, so the fourth core
  applies.
* If v=0, then u=3 and b+c=8-a<=7, so a=1 and b+c=7.
  The fifth core applies.

It remains to consider b<=1 and a>=2. Again u+v>=3 follows from
a+c<=7.

* If v=0, then u=3, b=1 and a+c=7; the fifth core applies.
* If v>=1 and a>=3, the sixth core applies.
* Otherwise a=2 and v>=1. If v>=2 and c>=2, the second core
  applies. If v=1, the total and c+u<=7 force b=1,c+u=7;
  hence c>=4,u>=2 and the fourth core applies. The only other
  possibility c<=1 is impossible because
  c+u+v=9-b>=8 but c+u+v<=7.

Thus u=0.

## 2. A failure has v<=1 {.unnumbered}

If v=2, the total and a+c,b+c<=7 imply a,b>=2. For c>=1
the third core applies; for c=0, a+b=9 implies a,b>=4 and the
eighth core applies.

If v=3, the same inequalities imply a,b>=1. For c>=2 the
seventh core applies. For c=1, a+b=7 and a,b<=5 give a,b>=2,
so the third core applies. For c=0, a+b=8 gives a,b>=3, so the
eighth core applies.

Consequently v<=1. Since a+c,b+c<=7,

  a>=4-v>=3, b>=4-v>=3.

## 3. A class of size at least four supplies an adjacent target {.unnumbered}

Now a+b+c=11-v>=10, so at least one class has size at least four.
Among its copies two have the same repeated colour; reserve them for the
two bichromatic corners of that class's target. The following six-corner
completions use only tricoloured corners and therefore ignore every
remaining repeated-colour label.

For A, the target corners are
01,02,04,31,32,34 (directed arcs). If a>=4 and c>=1, use A
for01,04; C for02; X for31,32; B for34. If a>=4 and v>=1,
instead use V for01 and A for02,04. If a=5, use three A for
01,02,04, two X for31,32, and B for34. When a=4, c+v>=1
follows from the total and b<=5, so these cases suffice.

For B, the corners are10,12,14,30,32,34. If b>=4 and c+v>=1,
use B for10,30; C or V for12; X for14,32; A for34. If b=5,
use three B for10,12,30; two X for14,32; A for34. Again the
total forces c+v>=1 when b=4.

For C, the corners are02,04,12,14,32,34. If c>=4, use two A
for02,04; two remaining C for12,14; X for32; B for34. Here
a>=3 and b>=3 ensure the required supplies.

Thus every pool in cover case54 is soluble. The earlier computation
enumerated13 opposite-failing count vectors in this case, but that number
is not used anywhere in this proof.



# Argument 22: Three identical opposite copies {#arg-22}

Assume a fourteen-failure contains three copies of an opposite variety.
The four-copy theorem already handles any opposite variety occurring
four times; hence assume each opposite multiplicity is at most three.
Normalize the three copies to X=O(0;12|34).

Hall's theorem supplies a cover C of at most four of X's eight corners,
with at least7+|C| nonanchor copies whose intersections with X lie in C.
The two-corner case is impossible by the established caps. The five
three-corner types are eliminated in Section6 of
[Argument 17](#arg-17). This uses the
explicit opposite-triangle extension lemmas from its preceding section.

If |C|=4, all eleven other sources belong to the indicated cover family.
The ten symmetry types are listed below. A bit mask is only an index
for the displayed corner subset, in order13,14,23,24,31,32,41,42.

| Cover corners | Mask | Orbit size | Hand argument |
|---|---:|---:|---|
|13,14,23,24|15|2|[Argument 11](#arg-11): exactly the5,3,3 family survives |
|13,14,23,31|23|8|[Argument 19](#arg-19) |
|13,14,24,31|27|16|[Argument 18](#arg-18) |
|14,23,24,31|30|8|[Argument 20](#arg-20) |
|13,14,31,32|51|8|[Argument 20](#arg-20) |
|13,23,31,32|53|4|[Argument 19](#arg-19) |
|14,23,31,32|54|16|[Argument 21](#arg-21) |
|14,24,31,32|58|4|[Argument 16](#arg-16), after symmetry |
|14,23,32,41|102|2|[Argument 19](#arg-19) |
|13,24,32,41|105|2|No source has its X-intersection contained in this cover |

The orbit sizes sum to70=binom(8,4). This is a geometric classification
of four directed arcs on a bidirected four-cycle, not an enumeration
of cube inventories. One can list it by the number of underlying edges
selected in both directions: zero, one, or two.

Only the first cover family can survive; its analysis forces
three identical opposite copies and adjacent-class sizes $5,3,3$.
Together with the four-copy theorem, this proves the necessary coarse
profiles for failures with an opposite multiplicity at least three.

The arguments for covers53 and54 use the existing eight-plus-three
missing-pair lemma from the paper. All other inputs are established
in this bundle or are the elementary directed-corner geometry.




# Argument 23: A common-corner 3,2,2,2,1 core always assembles {#arg-23}

**Lemma.** Suppose five distinct adjacent tricoloured classes containing
one common directed corner occur with multiplicities `3,2,2,2,1`.
These ten sources always admit an assembly, irrespective of their
repeated colours.

The proof consists of elementary six-corner completions and
repeated-colour pigeonhole arguments. It does not use a classification
of failed pools.

## 1. Notation and the five-class normal form {.unnumbered}

Normalize the common corner to `01`, write `Q={i,j,k}={2,3,4}`, and set

\[
P_i=C(0i),\qquad D_i=C(\{0\}\cup(Q\setminus\{i\})).
\]

Their pole pairs are `0i` and `1i`, respectively. Reversing every cut
and interchanging 0 and 1 exchanges the P and D families. We may
therefore suppose the absent class is `D_i`. The present classes and
their corners are

| Class | Corners |
|---|---|
| `P_i` | `01,0j,0k,i1,ij,ik` |
| `P_j` | `01,0i,0k,j1,ji,jk` |
| `P_k` | `01,0i,0j,k1,ki,kj` |
| `D_j` | `01,0j,i1,ij,k1,kj` |
| `D_k` | `01,0k,i1,ik,j1,jk` |

Write their multiplicities as `a,b,c,e,f`, respectively. Thus these
five positive numbers, in some order, are `3,2,2,2,1`.

An **own loop** means that, after reserving two copies of a class,
the other sources match all six corners of that class. In a failure,
a looped class must use a different repeated colour on every copy.
Two classes **conflict** if reserving one copy of each permits a
six-corner completion of a target whose two poles they can supply.
Conflicting classes must have disjoint repeated-colour sets.

We use the universal-restoration observation: a class with an own
loop conflicts with every present class whose pole pair meets its
own. Restore one reserved copy of the looped class and remove the
other class's reserved copy; the restored universal source replaces
that removed source if the six-corner matching had used it.

## 2. Four useful loop completions {.unnumbered}

The following facts follow directly from the corner table.

1. **If `a>=2`, then `P_i` has an own loop.** After reserving two
   `P_i`, use `P_j:0k`, `P_k:0j`, and an additional `P_j` or `P_k`
   at `01`. Such an additional copy exists because `b+c>=3`.
   Use `D_j:ij`, `D_k:ik`, and one remaining source from
   `D_j,D_k,P_i` at `i1`. There are enough because
   `e+f+a-2>=3`.
2. **If `b=3` and `f>=2`, then `P_j` has an own loop.** After the
   reservation, match
   `P_j:ji; D_k:j1,jk; P_i:0k; P_k:0i; D_j:01`.
3. **If `e=3`, then `D_j` has an own loop.** After the reservation,
   use `D_j:k1; P_i:ij; P_k:kj; D_k:i1; P_j:01`, and one additional
   `P_i` or `P_k` at `0j`. The last copy exists because `a+c>=3`.
4. **If `e=2` and `a=c=2`, then `D_j` has an own loop.** Use
   `P_i:0j,ij; P_k:k1,kj; D_k:i1; P_j:01` after reserving the two
   `D_j`.

We now locate the unique triple. Interchanging `j,k` leaves three
possibilities: `P_i`, `P_j`, or `D_j`.

## 3. The triple is `P_i` {.unnumbered}

The four classes `P_i,P_j,D_j,D_k` form a conflict clique.

The edge `P_i,P_j` follows from the own loop of `P_i`.
For the edge `P_i,D_j`, use target `P_j`. After reserving one of
each, the two remaining `P_i` fill `01,0k`, and `P_k` fills `0i`.
The three other target corners `j1,ji,jk` are filled by `P_j,D_k`:
use a `P_j` at `ji`, then two remaining copies at `j1,jk`.
There are at least three copies altogether because `b+f>=3`.
The edge `P_i,D_k` is symmetric.

For any pair among `P_j,D_j,D_k`, use target `D_j`: the reserved
pair can supply its poles `1j`. The three `P_i` fill `0j,i1,ij`.
Two sources from `P_k` and the unreserved `D_j` fill `k1,kj`.
At least two are available since `c+e>=3` and at most one `D_j`
was reserved. Any still unused source fills `01`; at this point
only seven of the ten sources have been reserved or used.

The looped triple needs three distinct repeated colours, and each
other member of the four-class clique needs another colour. Six
different colours would be required, which is impossible.

## 4. The triple is `P_j` {.unnumbered}

First suppose the singleton is `P_k` or `D_j`. Then `a=f=2`, so
`P_i` and `P_j` both have own loops. They conflict because their
pole pairs share 0. Their five required repeated colours would all
have to avoid 0, an impossibility.

If the singleton is `P_i`, then `c=e=f=2`. The looped triple
`P_j` conflicts with both `P_i,P_k`. These latter two also conflict:
reserve one of each and complete target `P_i` by

\[
D_j:i1,ij;\quad D_k:0k,ik;\quad
\text{remaining }P_k:0j;\quad P_j:01.
\]

The three classes need at least five different repeated colours,
all avoiding their common pole 0. This is impossible.

It remains that the singleton is `D_k`, so `a=c=e=2`. Both `P_i`
and `D_j` have own loops. The four classes `P_i,P_j,P_k,D_j` form
a conflict clique. Own-loop restoration gives the edges
`P_i,P_j`, `P_i,P_k`, and `D_j,P_j`. The other edges are witnessed
by the following completions, made after reserving the indicated pair.

| Reserved pair | Target | Six-corner completion |
|---|---|---|
| `P_i,D_j` | `P_j` | remaining `P_i:0k`; `P_k:0i`; remaining `D_j:01`; `P_j:ji,j1`; `D_k:jk` |
| `P_k,D_j` | `P_j` | `P_j:j1,ji,jk`; `P_i:01,0k`; remaining `P_k:0i` |
| `P_j,P_k` | `P_j` | remaining `P_j:ji,j1`; `D_k:jk`; `P_i:01,0k`; remaining `P_k:0i` |

The two looped doubles and the other two nonempty classes would
require `2+2+1+1=6` distinct repeated colours. This is impossible.

## 5. The triple is `D_j` {.unnumbered}

If `P_i` is not the singleton, then `a=2`. Thus `P_i` and `D_j`
are looped and both conflict with `P_j`. They also conflict with
one another. To see this, reserve one of each for target `P_j`.
Use remaining `P_i:0k`, `P_k:0i`, and remaining `D_j:01`.
The classes `P_j,D_k` fill the other three corners `ji,j1,jk`,
using `P_j` for `ji`; there are enough copies because `b+f>=3`.
This three-class clique would require `2+3+1=6` distinct repeats.

Finally let `P_i` be the singleton, so `b=c=f=2`. We show that
`D_j,P_i,P_j,P_k` form a clique. The edge `D_j,P_j` follows
from the own loop of `D_j`. The other five edges have these
completions.

| Reserved pair | Target | Six-corner completion |
|---|---|---|
| `P_i,P_j` | `P_i` | `D_j:0j,i1,ij`; `D_k:0k,ik`; `P_k:01` |
| `P_i,P_k` | `P_i` | `D_j:0j,i1,ij`; `D_k:0k,ik`; `P_j:01` |
| `P_j,P_k` | `P_j` | remaining `P_j:ji`; `D_k:j1,jk`; `P_i:0k`; remaining `P_k:0i`; `D_j:01` |
| `P_i,D_j` | `P_j` | `P_j:ji,j1`; `D_k:jk,0k`; `P_k:0i`; remaining `D_j:01` |
| `P_k,D_j` | `P_j` | `P_j:ji,j1`; `D_k:jk`; `P_i:0k`; remaining `P_k:0i`; remaining `D_j:01` |

The looped triple and the three other nonempty classes require
`3+1+1+1=6` distinct repeated colours. This final contradiction
proves the lemma.



# Argument 24: Nine cubes occupying all six classes through one corner {#arg-24}

**Theorem.** Suppose all six adjacent tricoloured classes containing a
fixed directed corner occur. Any nine cubes from those classes have an
assembly. Two useful eight-cube configurations also always assemble.

This is a hand proof. It uses only repeated-colour pigeonhole and the
explicit six-corner matchings below.

Normalize the common directed corner to `01`. Put `Q={i,j,k}={2,3,4}`
and write

\[
P_i=C(0i),\qquad D_i=C(0,Q\setminus\{i\}).
\]

Their pole pairs are respectively `0i` and `1i`. These six cuts all
contain `01`. Simultaneous cut reversal and interchange of 0 and 1
interchanges the `P` and `D` families.

Call a class looped when two copies with the same repeated colour
can provide bicoloured corners and the remaining sources match its
six tricoloured corners. Call two classes joined when copies with the
same repeated colour can do the analogous job. In a failure, a looped
class uses different repeated colours on all its copies; joined
classes have disjoint repeated-colour sets.

We use one elementary observation. If class `U` has an own-orientation
loop, it is joined to every present class `V` whose pole pair meets
its pole pair. Reserve one `U,V` for an `U` target's bicoloured
corners. Compared with the loop matching, a `U` copy is restored and
one `V` is removed; the restored universal `U` replaces that `V` if
it had been used in the six-corner matching.

## 1. A triple and five singletons already solve {.unnumbered}

Take three `P_i` and one copy of each other class. The class `P_i`
has a loop, as witnessed after reserving two copies by

\[
P_i:i1,\quad P_j:0k,\quad P_k:0j,\quad
D_i:01,\quad D_j:ij,\quad D_k:ik.
\]

The four classes `P_i,P_j,D_j,D_k` are pairwise joined:

* `P_i,P_j` are joined by the own-loop observation.
* For `P_i,D_j`, use target `P_j`: after reserving one of each,
  use remaining `P_i:01,0k`, `P_k:0i`, `D_i:ji`, `D_k:jk`,
  and `P_j:j1`. The `P_i,D_k` case is symmetric.
* Any two of `P_j,D_j,D_k` can supply the poles `1j` of target
  `D_j`. The three `P_i` fill `0j,i1,ij`, while `P_k` fills `kj`,
  `D_i` fills `k1`, and the unused member of that three-class group
  fills `01`.

Thus `P_i` requires three distinct repeats, and each of the other
three joined classes requires another repeat. Six different colours
would be needed. This proves the eight-cube statement with class
counts `3,1,1,1,1,1`. By symmetry a triple in any of the six classes
works.

## 2. Two opposite-index doubles and four singletons solve {.unnumbered}

Take two `P_i`, two `D_j` with `i!=j`, and one of each other class.
Both doubled classes have own loops:

| Reserved class | Six-corner completion |
|---|---|
| two `P_i` | `P_j:0k`; `P_k:0j`; `D_i:01`; `D_j:i1,ij`; `D_k:ik` |
| two `D_j` | `P_i:0j,ij`; `P_k:kj`; `D_i:k1`; `D_k:i1`; `P_j:01` |

The classes `P_i,D_j,P_j,D_i` form a conflict clique. Four of its
edges follow from the own-loop observation: `P_i` meets the poles of
`P_j,D_i`, and `D_j` meets those of `P_j,D_i`. The remaining two
edges have these direct completions after reserving the indicated
pair:

| Reserved pair | Target | Six-corner completion |
|---|---|---|
| `P_i,D_j` | `P_j` | remaining `P_i:0k`; `P_k:0i`; `D_i:ji`; `D_k:jk`; remaining `D_j:01`; `P_j:j1` |
| `P_j,D_i` | `P_i` | `P_i:01,0k`; `P_k:0j`; `D_j:i1,ij`; `D_k:ik` |

The two looped classes require two repeats each, and the other two
classes require one each. Again six different colours would be needed.

## 3. Three doubles in one family and three singletons solve {.unnumbered}

Take two of each `P_i,P_j,P_k` and one of each `D_i,D_j,D_k`.
All six classes are pairwise joined. Up to permutations of `i,j,k`,
there are four kinds of pair; these completions cover all of them.

| Reserved pair | Target | Six-corner completion |
|---|---|---|
| `P_i,P_j` | `P_i` | remaining `P_i:i1`; remaining `P_j:0k`; `P_k:0j`; `D_i:01`; `D_j:ij`; `D_k:ik` |
| `P_i,D_i` | `P_i` | remaining `P_i:i1`; `D_j:ij`; `D_k:ik`; `P_j:0k,01`; `P_k:0j` |
| `P_i,D_j` (`i!=j`) | `P_j` | `P_j:j1`; `D_i:ji`; `D_k:jk`; remaining `P_i:0k`; `P_k:0i,01` |
| `D_i,D_j` | `D_i` | `D_k:j1`; `P_j:0i,ji`; `P_k:k1,ki`; `P_i:01` |

Six pairwise disjoint nonempty repeated-colour sets cannot fit into
five colours. Interchanging the `P` and `D` families gives the
symmetric case with three doubled `D` classes.

## 4. Deduction for any nine cubes {.unnumbered}

If any class has at least three copies, Section 1 applies. Otherwise
each class has one or two copies, and at least three classes are doubled.
If doubles occur in both families, there is an opposite-index doubled
pair `P_i,D_j` with `i!=j`: with at least three doubled classes, not all
cross-family pairs can share the same index. Section 2 applies.
If all doubles are in one family, all three classes of that family
are doubled, and Section 3 applies.

Thus nine cubes occupying all six common-corner classes always solve.



# Argument 25: Pure fourteen-pools: the four-copy anchor, one-row cover {#arg-25}

**Proved by hand.** Suppose every adjacent class has at most four copies,
the pool is all-adjacent and has fourteen cubes, and A=C(01) has four
copies. Suppose every other source either is disjoint from A in
tricoloured corners or meets A only in the row 0→{2,3,4}. Then the pool
has an assembly.

Here C(S) is the cut S→Sᶜ. Put Q={2,3,4}. Besides A the permitted classes
are

    P_i=C(0i), D_i=C(0,Q\{i}), Z_i=C(Q\{i})  (i∈Q),
    B=C(Q).

Write p_i,d_i,z_i,b for their counts and z=b+Σz_i for the total of the
classes disjoint from A. There are ten nonanchor copies. Each disjoint
class has at most three copies: four A and four copies of any such
class build an opposite target. Also z≤5, since six disjoint copies
with individual counts≤3 match the six tricoloured corners of C(Q),
and two A with the same repeat supply its bichromatic corners.

## 1. Two disjoint-from-A sources already force an opposite target {.unnumbered}

For q,s∈Q distinct, the opposite target with bipartition01|qs is supplied
by four A in one direction and four other sources at

    q→0, s→0, q→1, s→1.

The first two positions see only the z zero-intersection sources. Let
n_q count nonzero-intersection sources whose outset contains q. The
four-position Hall conditions reduce to

    z−z_q≥1, z−z_s≥1,
    z−z_q+n_q≥2, z−z_s+n_s≥2,
    z+n_q≥3, z+n_s≥3.

The union of all four neighbourhoods has size10−p_r≥6, where
Q={q,s,r}; every other required union follows from these inequalities.

If z≥3, choose q,s for which z−z_q,z−z_s≥2. At most one index can fail
this bound, because two counts z_i≥z−1 would sum to more than z. The
displayed conditions hold, giving an assembly.

Suppose z=2. Let Z be the subset of Q appearing in the two zero-source
outsets, and N the subset appearing in the eight nonzero-source
outsets. Both have at least two elements: each zero outset has two or
three Q-elements, and eight nonzero sources cannot all be the single
class P_i of capacity four. If |Z∩N|≥2, select q,s in the intersection
and again apply the displayed conditions.

The only remaining case is Z={q,s}, N={s,r}. The two zero sources are
both Z_r, while all eight nonzero sources lie in P_s,P_r,D_q.
The shared-four bounds p_s+d_q≤7 and p_r+d_q≤7 imply p_s,p_r≥1;
one of them is at least two. Assume p_s≥2. Build the opposite target
with bipartition{q,s}|{1,r}, omitting0:

    two Z_r: q→1,q→r;
    two P_s: s→1,s→r;
    two A:   1→q,1→s;
    one P_r: r→s;
    another P_r or D_q: r→q.

The last source exists because p_r+d_q=8−p_s≥4. Thus every failure
would have z≤1.

## 2. No P or D class can have four copies {.unnumbered}

First suppose d_i=4, with Q={i,j,k}. Four D_i and two A fill six
corners of the opposite target1i|jk; the remaining positions are i→j
and i→k. If two other cubes match these, we are done. Otherwise
p_i≤1, and if p_i=1 then d_j=d_k=0; if p_i=0, at most one of d_j,d_k
is positive.

There are at least five nonzero sources outside D_i. Hence p_j+p_k>0:
otherwise those sources are P_i,D_j,D_k, and the preceding restrictions
give at most four of them. At least four sources belong to
P_j,P_k,D_j,D_k; each fits at least one of

    j→1,j→i,k→1,k→i,

and a source in P_j or P_k fits two. Two distinct sources therefore
match two distinct positions in this four-set. Reserve a same-repeat
pair from D_i; its remaining two copies fill the other two positions.
One A fills0→i, and an unused nonzero source fills0→1. This completes
the D_i target, a contradiction.

Now suppose p_i=4. Reserve its same-repeat pair. Two A can fill0→j,0→k,
and the two remaining P_i can fill two of0→1,i→1,i→j,i→k. Every
other nonzero source fits0→1; if d_j+d_k>0, one of them also fits an
i-row corner, so two other sources complete the four-set. The same
holds if the unique zero source contains i. Thus failure forces
d_j=d_k=0 and, when z=1, the zero source is Z_i.

Use the opposite target1i|jk again. Two A and two P_i fill its forward
half. The reverse half has row capacities p_j,p_k and a universal
pool of size d_i+z. These sum to six. Its four positions can fail Hall
only if p_j+d_i+z≤1 or p_k+d_i+z≤1, which would force the other p-count
to be at least five. This is impossible. Consequently p_i,d_i≤3.

## 3. The remaining opposite-target Hall conditions {.unnumbered}

Ignore the zero source if present. There are N=10−z∈{9,10} nonzero
sources, in six classes of capacity three. For target1i|jk, two A fill
1→j,1→k. Label its six other positions

    a=i→j, b=i→k, c=j→1, d=j→i, e=k→1, f=k→i.

The six source neighbourhoods are

|Class|Positions|
|---|---|
|P_i|a,b|
|P_j|c,d|
|P_k|e,f|
|D_i|c,d,e,f|
|D_j|a,e|
|D_k|b,c|

All Hall inequalities are automatic from N≥9 and the capacity-three
bounds except

    p_i+d_j≥1, p_i+d_k≥1, p_j+d_i≥1, p_k+d_i≥1;
    p_i+d_j+d_k≥2, p_j+p_k+d_i≥2;
    p_j+d_i+d_k≥2, p_k+d_i+d_j≥2.                 (*)

Classifying the zero coordinates in these six counts gives a short
description if all three opposite targets fail:

**Family I.** The main positive classes are P_j,P_k,D_i, where
{i,j,k}=Q. Their counts are at least two and sum to at least eight.
There may be one additional main class of count one.

**Family II.** P_i,D_j,D_k each have count three, every other main
count is zero, and z=1.

Here are details of that classification. With zero or one zero
coordinate, some choice of i satisfies(*). With exactly two zeros,
the matched pair p_i=d_i=0 also allows target i, as do two zero
p-counts. If d_j=d_k=0, all targets can fail only when p_i=1,
giving Family I. If p_i=d_j=0 with i≠j, the third target k succeeds
unless d_k=1, again Family I. With at least three zeros, N≥9 and
the capacity-three bound force exactly three nonzero counts, all
three. Three P-counts, three D-counts, or a mixed triple whose
minority index matches one of the majority indices solve directly
by(*). The two unmatched mixed triples are exactly Families I,II.

## 4. Both families contradict repeated-colour pigeonhole {.unnumbered}

In Family I put U=P_j,V=P_k,W=D_i. Their three counts are at least
two, and at least two counts equal three. Any class here of size
three must use three distinct repeats in a failure. To see this,
reserve a same-repeat pair and use these tricoloured completions:

* U target: remaining U at j→k; two W at j→1,j→i; one V at0→1;
  two A at0→i,0→k.
* V target: the symmetric assignment.
* W target: remaining W at0→1; two U at j→1,j→i; two V at k→1,k→i;
  one A at0→i.

Moreover any two of U,V,W must use disjoint repeat sets. For U,V,
one cube from each repeating r supplies the bichromatic corners of
the U target; its tricoloured completion uses one further U, two W,
one further V and two A as above. For U,W, use their poles0 and1
to make an A target: three A fill1→i,1→j,1→k, while one further W,
one further U and one V fill0→i,0→k,0→j. The V,W case is symmetric.
Thus the two size-three classes demand six different repeated
colours, impossible in a five-colour palette.

In Family II let U=P_i,V=D_j,W=D_k. U must use three distinct repeats:
after reserving a repeated pair, two A fill0→j,0→k, one V fills i→j,
one W fills i→k, another V or W fills i→1, and the remaining U fills0→1.

The zero source contains at least one of j,k; assume it contains k.
Then V also must use three distinct repeats. After reserving a V pair,
the remaining V fills k→j, the zero source fills k→1, three U fill
0→1,i→1,i→j, and one A fills0→j. Finally U and V cannot share a
repeat: reserve one from each for an A target's bichromatic corners;
four A fill the three1-row corners and0→i, and the remaining two U
fill0→j,0→k. Again six different repeats would be required.

Every case gives an assembly, proving the one-row-cover lemma.




# Argument 26: Four copies of an adjacent class: the other two three-corner covers {#arg-26}

This supplements [Argument 25](#arg-25). All assertions below are hand matching
arguments in the directed-cut model; the computation was used only to find
the cases. Let `C(S)` denote the cut from `S` to its complement. Fix

\[
A=C(01),\qquad a=4,
\]

and assume every class has at most four copies. A failure cannot have four
copies each of disjoint cuts, or more than seven copies in two cuts sharing
four arcs. In particular, the latter bound will be used for
`P=C(04)` with each of `D=C(034)` and `F=C(024)`.

The four cuts disjoint from `A` are

\[
B=C(234),\quad Z_2=C(34),\quad Z_3=C(24),\quad Z_4=C(23).
\]

Write `z` for their combined multiplicity. We use the established half-array
lemma: four `A`, one cut meeting `A` in a single arc, and any three cuts
disjoint from `A` build an opposite target. Thus `z<=2` whenever a singleton
intersection class is present.

An opposite target written `ab|cd` asks for all eight arcs between its two
pairs, in both directions. A statement assigning several arcs to one
class always uses that many distinct copies.

## 1. Hook cover `{02,03,12}` {.unnumbered}

Apart from zero-intersection cuts the allowed outside classes are

\[
P=C(04),\quad D=C(034),\quad F=C(024),\quad E=C(134).
\]

Their counts are `p,d,f,e`; all are at most four. Assume `e>0`, since
otherwise the one-row-cover lemma applies. Then

\[
e+p+d+f+z=10,\qquad p+d\le7,\quad p+f\le7.
\]

### Two zero cuts {.unnumbered}

If one of the two zeros contains colour 3, target `01∣34` works. Use four
`A` for the forward half. Use a `P,D,F` copy for `41`, an `E` for one of
`30,40`, and the two zeros for `31` and the other of `30,40`. The two zeros
can be assigned this way: if the zero used for `31` contains 4, swap their
roles if necessary; a zero missing 3 is exactly `C(24)` and supplies `40`.
Every zero contains at least one of 3 and 4.

If neither zero contains 3, both are `C(24)`. Target `01∣24` uses four `A`
for the forward half and the two zeros, `E`, and a `P,D,F` copy for
`20,21,40,41`, respectively. A `P,D,F` copy exists because `e<=4`.
Consequently `z<=1` in a failure.

### One zero cut {.unnumbered}

If `d>0`, then `p+f>0`, because otherwise `e+d=9>8`. Target `01∣34`
uses four `A`, then `D` for `31`, a `P,F` for `41`, and `E` and the zero
for `30,40`. Hence `d=0`.

Now `e+p+f=9` and `p+f<=7`, so `e>=2` and `p,f>=1`. If the zero is
`Z_3=C(24)`, target `01∣24` uses four `A`, then zero:`20`, `F:21`,
`E:40`, and `P:41`.

Every other zero contains 3 and supplies `30`. If `f>=2`, target `02∣13`
is given by

| Class | Arcs |
|---|---|
| `A` | `03,12` |
| `E` | `10,32` |
| zero | `30` |
| `F` | `21,23` |
| `P` | `01` |

If `f=1`, necessarily `p=e=4`. Then `P` has a loop: reserve two
same-repeat `P` cubes for its two bicoloured corners, and fill its six
tricoloured corners by remaining `P:01,43`, `A:02,03`, `E:42`, `F:41`.
Four copies of a class force a repeated repeat colour, so this solves.

### No zero cuts {.unnumbered}

If `e>=2` and `d>=1`, target `01∣34` uses four `A`, two `E` at `30,40`,
one `D` at `31`, and another `P,D,F` at `41`. Thus `e>=2` implies `d=0`
in a failure. Then `e+p+f=10`, so `e>=3` and `p,f>=2`. Target `02∣13`
uses `A:03,12`, `E:10,30,32`, `F:21,23`, `P:01`.

The only remaining possibility has `e=1` and `p+d+f=9`. The bounds
`p+d,p+f<=7` imply `d,f>=2`. A class of size four has a loop, as follows;
the class in the first column has two copies reserved for the bicoloured
corners.

| Reserved class | Its six tricoloured corners |
|---|---|
| `P` | `A:02,03`; `D:42`; `F:43`; remaining `P:01,41` |
| `D` | remaining `D:31,01`; `A:02`; `E:32`; `P:42`; `F:41` |
| `F` | remaining `F:21,23`; `A:03`; `P:43`; two further `P,D:01,41` |

In the last row `p+d=5`, so the further copies exist. The other rows have
all displayed classes present by the preceding count bounds. Thus a
failure would require `p=d=f=3`.

For this last case use the thirteen-cube-core lemma in
[Argument 25](#arg-25): `A^4,P^3,D^3,F^3` plus any cut containing one of
`21,31,23,32` solves. Here `E=C(134)` contains `32`.

This proves the hook-cover case.

## 2. Disjoint cover `{02,03,14}` {.unnumbered}

Use the same `P,D,F`, but now

\[
E=C(123),
\]

with `e>0`; again `e+p+d+f+z=10` and `z<=2`. In addition to `p+d,p+f<=7`
we may assume `p+e<=7`, since `P` and `E` are reverse cuts and four of
each solve an opposite target.

The following small assemblies will be used:

* `2A+2P+2D+F+E` builds `12∣34`: `A:13,14`, `E:24`, `F:23`,
  `D:31,32`, `P:41,42`.
* Interchanging 2 and 3 gives `2A+2P+D+2F+E` building `13∣24`.
* `2A+4D+F+E` builds `12∣34`: `A:13,14`, `E:24`, `F:23`, and `D`
  fills all four reverse arcs. There is a symmetric version with `4F+D`.

### A zero containing 4 {.unnumbered}

If `d>0` and a zero contains 4, target `01∣34` uses four `A`, `E:30`,
zero:`40`, `D:31`, and one further `P,D,F:41`. If `f>0`, use the
colour-swapped target `01∣24`. There is always a further non-`E` copy
because `p+d+f=10-z-e>=4`. Also `d=f=0` would force `p+e>=8`, forbidden.

Therefore any zero in a failure is `Z_4=C(23)`.

### Two copies of `Z_4` {.unnumbered}

If `e>=2`, use target `14∣23`. Two `A` fill `12,13`, two `E` fill
`24,34`, the two zeros fill `21,31`, and two `P,D,F` fill `42,43`.
These last two arcs can be matched unless `p+d=0` or `p+f=0`; there are
at least four copies in `P,D,F`. In either exceptional case the entire
non-`E` multiplicity is four in `D` or `F`, and `e=4`. These two cuts
are disjoint, so their eight cubes already solve.

If `e=1`, then `p+d+f=7`, whence `p+d,p+f>=3`. At least one of `d,f`
is positive. Suppose `d>0`; the other case is symmetric. Target `14∣23`
uses `A:12,13`, `E:24`, zeros:`34,21`, `D:31`; the remaining sources
match `42,43` because their degrees are at least two and three,
respectively. Thus this case also solves.

### One copy of `Z_4` {.unnumbered}

If `e>=3`, target `04∣13` uses `E:10,30,34`, `A:14,03`, a `P,F`
copy at `43`, and two further `P,D,F` copies at `01,41`. Here
`p+d+f=9-e>=5`, and `p+f>0` since `d<=4`.

If `e=2`, then `p+d+f=7` and `p+d,p+f>=3`. As in the previous case,
choose `D` if `d>0` (otherwise interchange 2 and 3). Target `14∣23`
uses `A:12,13`, `E:24,34`, zero:`21`, `D:31`, and two remaining
`P,D,F` copies for `42,43`.

If `e=1`, then `p+d+f=8`. Both `d,f` are positive: otherwise a
shared-four-arcs pair has total eight. If `p>=2`, at least one of `d,f`
is at least two, and the corresponding first or second small assembly
above applies. If `p<=1`, at least one of `d,f` equals four, and the
third small assembly or its symmetric version applies.

### No zero cuts {.unnumbered}

If `e=1`, then `p+d+f=9`; the same small assemblies apply (both `d,f`
are positive, and if `p<=1` one is four).

Suppose `e>=2` and `d,f>0`. Target `14∣23` uses `A:12,13`, `E:24,34`,
`D:31`, `F:21`, and two remaining `P,D,F` at `42,43`. Both last degrees
are positive and their union has at least four copies: indeed
`p+d+f=10-e>=6`, so `p+d,p+f>=2` before removing `D,F`.

Finally suppose, say, `d=0`. Then `e+p+f=10` and `p+e,p+f<=7` give
`e,f>=3`; also `p>0`. Target `04∣13` uses `E:10,30,34`, `A:14`, and
four `P,F` copies for its forward half. Since `p+f=10-e>=6`, this is
possible.

This proves the disjoint-cover case. Together with the one-row lemma,
all three-corner covers without source exceptions are now settled.



# Argument 27: Four copies of an adjacent class: covers with source exceptions {#arg-27}

This completes the pure fourteen-cube case with a tricoloured class of
size four, assuming the established bound that no class has more than
four copies. The three-corner covers are handled in [Argument 25](#arg-25) and
[Argument 26](#arg-26).

## Normal form and a useful zero-cut lemma {.unnumbered}

Write `C(S)` for the directed cut from `S` to its complement in
`{0,1,2,3,4}`. Fix `A=C(01)` with four copies. Its six arcs form the
two-row, three-column array

\[
\{02,03,04;12,13,14\}.
\]

The cuts disjoint from `A` are `B=C(234)` and `Z_i=C({2,3,4}\setminus{i})`
for `i=2,3,4`. Call their combined count `z`.

**Four-zero lemma.** Four `A` and any four zero cuts build an opposite
target. Choose two colours `q,s` in `{2,3,4}` each contained in at least
two of the four zero outsets. Such a choice exists because at most one
of the three counts of `Z_i` exceeds two. Every zero contains `q` or `s`.
Hence their four copies match `q0,q1,s0,s1`: each row has degree at least
two and the union of the rows sees all four copies. Four `A` fill the
forward half of target `01|qs`.

Thus `z<=3` in a failure. We also use the established half-array lemma
that four `A`, a cut meeting `A` in one arc, and any three zero cuts
build an opposite target. If a singleton-intersection class is present,
then `z<=2` in a failure.

Two of the four `A` copies have the same repeated colour. Reserve them
for the bicoloured corners of their own target. If the ten outsiders
have matching rank at least four on the six arcs of `A`, four of them
and the remaining two `A` complete the target. Therefore their rank is
at most three. By Konig's theorem, they admit a cover by `c` corner
vertices and at most `3-c` individual source copies.

For `c=0` or `1`, removing at most three or two source copies leaves at
least seven zeros, or at least eight copies in one singleton class and
the zero classes. The former contradicts `z<=3`; the latter contradicts
the sum of the bounds four and three. Thus only `c=2,3` remain.

## Two-corner covers in different rows {.unnumbered}

If the two corners lie in a column, normalize them to `{02,12}`. Apart
from one exceptional source, the outsiders are zero cuts and the two
singleton classes `D=C(034), E=C(134)`. Their counts satisfy `d+e+z=9`.
There is a singleton class, so `z<=2`; thus `d,e>=3`. But target
`01∣34` is filled by four `A`, `D:31,41`, and `E:30,40`.

If the two corners are in distinct columns, normalize them to `{02,13}`.
The two singleton classes are now `D=C(034), E=C(124)`, again with
`d,e>=3`. Target `03∣12` is filled by `A:02,13`, `D:01,31,32`, and
`E:10,20,23`.

Consequently a cover with a source exception must have its two corners
in the same row.

## Two corners in one row {.unnumbered}

Normalize the corners to `{02,03}`. The nonzero normal classes are

\[
P=C(04),\quad D=C(034),\quad F=C(024),
\]

with counts `p,d,f`. There is one exceptional cube `E`, and

\[
p+d+f+z=9,\quad p,d,f\le4,\quad p+d,p+f\le7.
\]

The last inequalities follow from the shared-four-arcs bound. There is
at least one `D` or `F`: otherwise `p+z=9` contradicts `p<=4,z<=3`.
Thus `z<=2`.

If `E` contributes at most one corner outside `{02,03}`, all outsiders
have a three-corner cover, already settled. Otherwise, up to swapping
2 and 3, `E` is one of

\[
C(14),\quad C(12),\quad C(014),\quad C(013).
\]

These are respectively an aligned opposite-row pair, a skew opposite-row
pair, an aligned four-corner rectangle, and a skew rectangle. In
particular, every remaining `E` contains an arc of the second row of `A`.

### Completion and conflict lemmas {.unnumbered}

The following statements make the subsequent counting short. A loop on
a class means that any two copies of that class with the same repeated
colour build a target after adding six further cubes. An edge between
two classes means the analogous statement for one reserved cube from
each class. Thus looped classes use distinct repeated colours in a
failure, and joined classes use disjoint sets of repeated colours.

**Heavy-class completions.** Suppose `p,d,f>0` and one count is four.
It has a loop. Reserve two of that class; the following table gives the
six tricoloured corners, using remaining copies.

| Class of size four | Completion |
|---|---|
| `P` | `A:02,03`; `D:42`; `F:43`; remaining `P:01,41` |
| `D` | remaining `D:31,32`; `A:02`; `P:42`; `F:41`; one further `P,F:01` |
| `F` | remaining `F:21,23`; `A:03`; `P:43`; `D:41`; one further `P,D:01` |

The further copy in the last two rows exists since the other two counts
sum to `5-z>=3`. A size-four loop solves by the pigeonhole principle.

**Small conflict clique.** Suppose `p,d,f>=2`, at least one of `d,f`
is at least three, and `E` has a second-row arc of `A`. Then `A,P,D,F`
are pairwise joined, and `P` has a loop.

For the loop on `P`, reserve two `P` and use `A:02,03`, `D:01,42`,
`F:41,43`. To join `A` to any one of `P,D,F`, use target `A`: after
reserving one copy of each endpoint, three `A` remain; two normal
copies fill `02,03` and `E` fills a second-row arc, while the three `A`
fill the other three positions. The endpoint pole pairs permit its
two bicoloured corners: `P` supplies pole 0, and `D,F` supply pole 1.

To join `P,D`, use target `A`, with bicoloured corners supplied at poles
0 and 1. Four `A` remain, and a remaining `P` and an `F` supply `02,03`.
The `P,F` edge is symmetric. Finally, if `f>=3`, use target `F` for
the `D,F` edge: after reserving one of each, fill its tricoloured corners
by remaining `F:21,23`, `P:01,43`, remaining `D:41`, and `A:03`.
If `d>=3` instead, interchange 2 and 3.

In particular, if `p=3` this clique requires at least `1+3+1+1=6`
different repeated colours, impossible with five colours.

If `p=2,d=f=3` and a zero cube is also available, that zero contains
2 or 3. If it contains 3, `D` has a loop: reserve two `D` and fill by
remaining `D:32`, zero:`31`, `A:02`, `P:41,42`, `F:01`.
If it contains 2, the symmetric construction loops `F`. The clique
`A,P,D` or `A,P,F` then requires `1+2+3=6` different repeated colours.

### No zero cubes {.unnumbered}

Here `p+d+f=9`. The shared-four-arcs bounds imply `d,f>=2`, and `p>=1`.
If any count is four, the heavy-class completion solves. Otherwise all
three counts equal three, and the small conflict clique solves.

### One zero cube {.unnumbered}

Here `p+d+f=8`, and `d,f>=1`. If `p>0`, a size-four count solves by the
heavy-class completion. Otherwise the counts are a permutation of
`2,3,3`, covered by the small conflict clique and its zero-cube extension.

If `p=0`, then `d=f=4`. There are only the four exceptional source
types listed above:

* If `E=C(14)` or `C(014)`, it contains `42`. Reserve two `D`, then
  use remaining `D:31,32`, `A:02`, `F:01,41`, `E:42`. This is a loop
  on `D`.
* If `E=C(12)`, target `12∣34` uses `A:13,14`, `E:24`, `F:23`, and
  four `D` for all four reverse arcs.
* If `E=C(013)`, target `13∣24` uses `A:12,14`, `E:34`, `D:32`, and
  four `F` for all four reverse arcs.

### Two zero cubes {.unnumbered}

Four `A` fill the forward half of any target `01|qs`, with `q,s` in
`{2,3,4}`. The two zero cubes fill `q0,s0` unless both are the same
`Z_i` with `i` equal to `q` or `s`. Once these are filled:

* pair `{3,4}` works if `d>0`, using `D:31` and any further `P,D,F:41`;
* pair `{2,4}` works if `f>0`, symmetrically;
* pair `{2,3}` works if `d,f>0`, using `F:21,D:31`.

Since `p+d+f=7`, at least one of `d,f` is positive. If the zeros differ,
or one is `B`, the first or second construction therefore solves.
If both zeros are `Z_2`, failure forces `d=0`; if both are `Z_3`,
it forces `f=0`; if both are `Z_4`, it forces at least one of `d,f`
to vanish. Up to swapping 2 and 3, the only remaining possibility is
`d=0`, `p+f=7`, hence `(p,f)=(4,3)` or `(3,4)`.

For `(4,3)`, `P` has a loop: reserve two `P` and use remaining `P:01,42`,
`A:02,03`, `F:41,43`. For `(3,4)`, `F` has a loop: reserve two `F` and
use remaining `F:21,23`, `A:03`, and `P:01,41,43`.

All source-exception covers are now excluded. Together with the three
corner-cover lemmas, this proves that any pure fourteen-cube pool with
maximum tricoloured-class count four has an assembly.



# Argument 28: Six doubled adjacent classes {#arg-28}

**Elementary theorem.** Take two cubes from each of six distinct adjacent
tricoloured-corner classes. If their tricoloured-corner union supports an
opposite-repeat target, these twelve cubes assemble an opposite target.
The repeated colours within the six classes are irrelevant.

Write C(S) for the directed cut S→Sᶜ on five colours, where |S| is two
or three. Opposite targets are the eight directed edges of a bidirected
four-cycle. Only tricoloured corners are used in this proof.

## 1. A failed supported target has three private corners {.unnumbered}

Fix an opposite target T with halves P→Q and Q→P, where |P|=|Q|=2;
the fifth colour is omitted. The intersections of adjacent classes
with T have the following elementary description.

* Two classes contain the whole half P→Q, and two the whole half Q→P.
* Eight classes give a two-corner row or column in one of the two halves,
  one class for each such row or column.
* The other eight classes give four pairs crossing between the halves,
  two classes per pair. Each corner belongs to exactly one such pair.

The row/column pairs form a four-cycle in each half; the four doubled
pairs form a matching between the halves. It follows that at most three
classes have their entire intersection with T inside any prescribed
three corners, and at most two inside any prescribed two corners.
For the three-corner assertion, three corners in one half contain at
most two row/column pairs. If the corners lie in both halves, they
contain at most one row/column pair and one doubled pair.

Now each of our six classes supplies two sources. A set of one or two
target corners has enough neighbours because T is supported. A set of
five corners sees at least three classes, hence six sources: its
complement contains at most three complete source intersections.
A set of six corners similarly sees at least four classes, and a set
of seven or eight sees all six classes. Thus Hall can fail only on
three or four corners, all supplied by one class A.

Such a class must contain one whole target half, since all other
intersections have size two. In particular A has three target corners
that no other selected class contains.

## 2. Three private corners force a different opposite assembly {.unnumbered}

Reverse all cuts if necessary, and relabel colours, to put

    A=C(01),   H={03,04,13}.

Here ab denotes the directed corner a→b. The three corners H are
private to A. The classes avoiding H are exactly the following eight:

    U = { C234, C134, C123, C034 },
    V = { C13, C23, C24, C34 }.

This list follows directly from the implications 0∈S⇒3,4∈S and
1∈S⇒3∈S for an outset S of size two or three.

Our five other distinct classes therefore include three from U or
three from V. Two copies of A and two copies of any such three classes
already build an opposite target, as follows.

### Three classes from U {.unnumbered}

If C234 is present, use the target with bipartition 01∣24.
C234 supplies any two of the reverse corners {20,21,40,41}.
The other three members of U have these two-corner intersections:

| Class | Forward corner | Reverse corner |
| --- | --- | --- |
| C134 | 12 | 40 |
| C123 | 14 | 20 |
| C034 | 02 | 41 |

For either two of these classes, use one copy at its listed forward
corner and the other at its listed reverse corner. The two A copies
fill the two remaining forward corners, and the two C234 copies fill
the two remaining reverse corners.

If C234 is absent, the classes are C134,C123,C034. Use target 04∣12:

| Sources | Assigned corners |
| --- | --- |
| 2 C01 | 02,14 |
| 2 C134 | 10,42 |
| 2 C123 | 20,24 |
| 2 C034 | 01,41 |

### Three classes from V {.unnumbered}

If C13 is present, use target 01∣24. The two A copies fill 02,04,
and the two C13 copies fill 12,14. The other two classes are selected
from C23,C24,C34. C23 supplies 20,21; C34 supplies 40,41; and C24
can supply either pair. Thus the reverse half can always be filled.

If C13 is absent, use target 12∣34:

| Sources | Assigned corners |
| --- | --- |
| 2 C01 | 13,14 |
| 2 C23 | 24,31 |
| 2 C24 | 23,41 |
| 2 C34 | 32,42 |

Every case supplies a different opposite assembly. This contradicts
the assumed failure of all opposite targets, and proves the theorem.

## Corollary: six repeated classes suffice in a pure fourteen-pool {.unnumbered}

**Theorem.** Fourteen adjacent-repeat cubes are soluble whenever at
least six distinct tricoloured-corner classes each occur at least twice.

In a hypothetical failure, pure concentration first bounds every class
by three: use [Argument 13](#arg-13), [Argument 12](#arg-12),
and the four-copy proofs [Argument 25](#arg-25),
[Argument 26](#arg-26),
[Argument 27](#arg-27). None uses this corollary.
Select two copies from six such classes. The theorem above solves if
their union supports an opposite target. Otherwise the support-poset theorem in
[Argument 15](#arg-15) places the six distinct classes in one
of the two six-class families below; thus they fill that family exactly.

### Common-corner family {.unnumbered}

Write the common corner as a→b, and the other colours as i,j,k.
The six classes are A_i=C(ai), A_j=C(aj), A_k=C(ak), and
B_i=C(ajk), B_j=C(aik), B_k=C(aij), two copies of each.

Each A_i has a loop: after its two copies have been reserved for the
bicoloured corners, fill its six tricoloured corners by

    B_j: ij, ib;   B_k: ik, ak;   A_k: aj, ab.

Consequently, in a failure the two A_i copies must have different
repeated colours. Also A_i and A_j cannot share a repeated colour.
Indeed reserve one of each for the bicoloured corners of an A_i target,
using their common pole a. Relative to the displayed loop completion,
one universal A_i copy has been restored and one A_j copy removed;
the restored A_i can replace the removed source if it was used.
Thus the three A classes would require six different repeated colours,
which is impossible. The twelve selected cubes already solve.

### Butterfly family {.unnumbered}

Normalize the six classes to

    C01, C02, C124, C123, C12, C012.

Their union misses exactly 31,32,41,42. Any adjacent class outside
these six contains one of these four corners: avoiding all four means
being an upset of the two-below-two order, whose size-two and size-three
upsets are exactly the six listed sets.

By symmetry suppose an outside source Y contains 31. The target 03∣14
is assembled using Y and seven of the eight high-class copies:

| Sources | Corners |
| --- | --- |
| Y | 31 |
| 2 C01 | 04,13 |
| C02 | 01 |
| 2 C124 | 40,43 |
| 2 C123 | 10,34 |

Thus any outside source gives an opposite assembly. If all fourteen
sources lie within the butterfly family, the cap-three butterfly profile lemma in the same reference says that
a failure has class counts 3,3,3,3,1,1.
That is incompatible with all six classes occurring at least twice.
This proves the corollary.



# Argument 29: Nine distinct adjacent classes: an explicit Hall-table proof {#arg-29}

**Status.** This is a finite Hall-table proof, with the complete small
certificate displayed below. A computer was used to find and audit the
table. Unlike the six-doubled-classes lemma, this has not yet been reduced
to a conceptual geometric argument. Its only finite calculations concern
five fixed sources and at most four of one target's eight corners; no
fourteen-cube inventory enumeration is assumed. The Hall reduction and
table dominance were independently audited from the directed-cut model.

**Theorem.** One cube from each of any nine distinct adjacent
tricoloured-corner classes has an opposite-target assembly.

Write `S` for the class C(S)=S→Sᶜ, where S has size two or three.
Write `ab` for the directed corner a→b. A target `ab|cd` consists of
all eight directed corners between its two pairs. Repeated colours do
not enter this lemma.

## 1. Six possible cores {.unnumbered}

Call a class positive when its outset has size two. Simultaneous reversal
interchanges the two orientations, so at least five of our nine distinct
classes may be assumed positive. Regard any five of these as five edges
on the five colours. Up to relabelling, a five-edge simple graph on five
vertices has the following six forms: a triangle with two leaves at one
vertex; a diamond and an isolated vertex; a triangle with leaves at two
vertices; a triangle with an attached two-edge path; a four-cycle with a
leaf; or a five-cycle. These are the six cores in the tables below.

This graph list can be checked from its cycles. A triangle-free five-edge
graph is the five-cycle or a four-cycle with a leaf. With a triangle,
the two remaining edges either complete a diamond, attach a path, or
attach the two extra vertices to the same or different triangle vertices.

Let H be the four remaining, distinct helper classes. None belongs to
its chosen five-class core.

## 2. The Hall calculation used by every table row {.unnumbered}

Fix a target T and a set S of its corner positions. Put

    a(S) = number of the five core classes meeting S,
    D(S) = helper classes disjoint from S,
    k(S) = |S|−1−a(S).

The Hall inequality for S fails exactly when

    |H \ D(S)| ≤ k(S).                              (1)

Every source meets T in either two or four positions. At most three
classes have their entire intersection inside any three positions;
at most two have it inside any two positions. These facts follow
from the two square halves and the four doubled cross-pairs described
in [Argument 28](#arg-28). For nine distinct sources, therefore,
Hall is automatic for sets of at least five positions. Only |S|≤4
needs to be considered in (1).

If a(S)≥|S|, there is no obstruction. If a(S)=|S|−1, condition (1)
says H⊆D(S); it is impossible when |D(S)|<4. Such a set S can be
discarded when it contains a smaller core-deficient set, since that
smaller set has a larger D-set. The only higher-deficiency sets of
size at most four occur for the first core; they are recorded in
Section 4. This gives a short way to check completeness of the tables.

A useful general dominance rule is the following. An obstruction
`|H \\ D|≤k` implies a listed obstruction `|H \\ E|≤l` whenever

    |D \\ E| + k ≤ l.

Indeed at most |D\\E| helpers can lie in D outside E, and at most k
helpers lie outside D. This checks the table reductions without
enumerating possible helper collections.

## 3. Possible helper sets when a target fails {.unnumbered}

In the following tables, a normal row means all four helpers must lie
in the displayed D-set. A row with k=1 instead means at most one helper
lies outside D. For k=1 the displayed D has three members, so all three
must be present. The corner set S is supplied to make each obstruction
checkable directly from the cut definition.

### Core 1: {01, 02, 03, 04, 12} {.unnumbered}

| Target | Corner set S | D(S) | k |
| --- | --- | --- | ---: |
| 14∣23 | {31,34} | {134, 124, 024, 14, 014, 24, 012} | 0 |
| 14∣23 | {42,43} | {234, 123, 13, 023, 23, 013, 012} | 0 |
| 02∣14 | {40} | {123, 034, 13, 024, 023, 23, 014, 013, 012} | 0 |
| 02∣14 | {10,21,24,40} | {034, 014, 013} | 1 |
| 02∣13 | {30} | {124, 034, 024, 14, 023, 014, 24, 013, 012} | 0 |
| 02∣13 | {10,21,23,30} | {034, 014, 013} | 1 |

The first target forces H into one of its two seven-element sets, neither of which contains `034`. Thus the k=1 alternatives for the other two targets are impossible, since both require `034`. The intersection of a first-target set with both remaining k=0 sets has only three members: respectively `{024,014,012}` or `{023,013,012}`. Four distinct helpers cannot lie there.

### Core 2: {01, 02, 03, 12, 13} {.unnumbered}

| Target | Corner set S | D(S) | k |
| --- | --- | --- | ---: |
| 02∣13 | {10,21,23,30} | {04, 034, 014, 013} | 0 |
| 02∣13 | {01,21,30,32} | {124, 14, 014, 012} | 0 |
| 03∣12 | {01,20,23,31} | {134, 14, 014, 013} | 0 |
| 03∣12 | {10,20,31,32} | {04, 024, 014, 012} | 0 |

Every D-set for the first target meets every D-set for the second in at most 2 classes. Hence four distinct helpers cannot make both targets fail.

### Core 3: {01, 02, 03, 12, 14} {.unnumbered}

| Target | Corner set S | D(S) | k |
| --- | --- | --- | ---: |
| 02∣14 | {10,21,24,40} | {04, 034, 014, 013} | 0 |
| 02∣14 | {40,42} | {123, 13, 024, 023, 23, 013, 012} | 0 |
| 03∣12 | {01,20,23,31} | {134, 13, 014, 013} | 0 |
| 03∣12 | {31,32} | {124, 04, 123, 024, 014, 24, 012} | 0 |

Every D-set for the first target meets every D-set for the second in at most 3 classes. Hence four distinct helpers cannot make both targets fail.

### Core 4: {01, 02, 03, 12, 34} {.unnumbered}

| Target | Corner set S | D(S) | k |
| --- | --- | --- | ---: |
| 01∣24 | {12,14,20} | {04, 034, 024, 023} | 0 |
| 01∣24 | {40,41} | {123, 13, 023, 23, 014, 013, 012} | 0 |
| 02∣13 | {03,10,12,23} | {234, 034, 023, 23} | 0 |
| 02∣13 | {10,21,23} | {04, 034, 014, 013} | 0 |
| 02∣13 | {01,21,30,32} | {124, 14, 014, 012} | 0 |

Every D-set for the first target meets every D-set for the second in at most 2 classes. Hence four distinct helpers cannot make both targets fail.

### Core 5: {01, 02, 03, 14, 24} {.unnumbered}

| Target | Corner set S | D(S) | k |
| --- | --- | --- | ---: |
| 03∣24 | {32,34} | {234, 124, 04, 12, 024, 014, 012} | 0 |
| 03∣24 | {20,40,43} | {034, 13, 023, 013, 012} | 0 |
| 02∣14 | {10,21,24,40} | {04, 034, 014, 013} | 0 |
| 02∣14 | {10,42} | {234, 024, 023, 23, 013, 012} | 0 |

Every D-set for the first target meets every D-set for the second in at most 3 classes. Hence four distinct helpers cannot make both targets fail.

### Core 6: {01, 02, 13, 24, 34} {.unnumbered}

| Target | Corner set S | D(S) | k |
| --- | --- | --- | ---: |
| 01∣23 | {02,13} | {234, 134, 123, 024, 023, 23} | 0 |
| 01∣23 | {03,13,20,21} | {134, 03, 034, 013} | 0 |
| 01∣23 | {02,12,30,31} | {124, 12, 024, 012} | 0 |
| 02∣13 | {01,21,23} | {134, 123, 14, 014, 013} | 0 |
| 02∣13 | {10,30,32} | {04, 024, 023, 014, 012} | 0 |

Every D-set for the first target meets every D-set for the second in at most 2 classes. Hence four distinct helpers cannot make both targets fail.

## 4. Completeness details for the small Hall tables {.unnumbered}

For each core and target, the next table lists **all inclusion-minimal
core-deficient corner sets of size at most four**, before discarding
those with fewer than four available avoiding helper classes. The number in parentheses is |D(S)|. In all these sets,
a(S)=|S|−1. Every other deficit-one set contains one listed here, and
its D-set is a subset of that listed set's D-set.

| Core | Target | Minimal core-deficient sets S, with |D(S)| |
| --- | --- | --- |
| 1 | 14∣23 | {31,34} (7); {42,43} (7); {12,13,21,24} (2) |
| 1 | 02∣14 | {40} (9); {10,21,24} (4) |
| 1 | 02∣13 | {30} (9); {10,21,23} (4) |
| 2 | 02∣13 | {01,21,30,32} (4); {03,12,21,30} (2); {10,21,23,30} (4) |
| 2 | 03∣12 | {01,20,23,31} (4); {02,13,20,31} (2); {10,20,31,32} (4) |
| 3 | 02∣14 | {40,42} (7); {10,21,24,40} (4); {10,21,24,42} (1) |
| 3 | 03∣12 | {31,32} (7); {01,20,23,31} (4); {01,20,23,32} (1) |
| 4 | 01∣24 | {40,41} (7); {12,14,20} (4); {02,04,12,21} (2) |
| 4 | 02∣13 | {03,12,21} (3); {10,21,23} (4); {01,21,30,32} (4); {03,10,12,23} (4) |
| 5 | 03∣24 | {32,34} (7); {20,40,43} (5) |
| 5 | 02∣14 | {10,42} (6); {10,21,24,40} (4); {21,24,40,42} (2) |
| 6 | 01∣23 | {02,13} (6); {02,03,20,21} (2); {02,12,30,31} (4); {03,13,20,21} (4); {12,13,30,31} (2) |
| 6 | 02∣13 | {01,21,23} (5); {10,30,32} (5); {01,03,10,12} (2) |

The only deficit-two sets of size at most four are, for Core 1:

* target `14∣23`: S={31,34,42,43}, with only one avoiding helper class,
  so four helpers cannot satisfy k=1;
* target `02∣14`: S={10,21,24,40}, giving its k=1 row above;
* target `02∣13`: S={10,21,23,30}, giving its k=1 row above.

There are no larger deficits for |S|≤4. For the first core, the deficit-one triple in either of the last two
targets is already covered by its displayed deficit-two four-set: its
four-element avoiding set consists of the three-element D-set plus one
additional class. This explains why no separate row is needed.

This completes the Hall reduction
and the six-case proof.

## Consequence for fourteen cubes {.unnumbered}

An opposite-unsoluble all-adjacent pool has at most eight occupied
tricoloured-corner classes. If a fourteen-pool had every class count
at most two, at least six of those classes would have count two.
The corollary in [Argument 28](#arg-28) would then solve it.
Thus a pure fourteen-cube failure has a class of size at least three.

Together with the separate four- and five-class proofs and the older
six-class bound, every pure fourteen-cube failure has maximum class
count exactly three. This does not yet prove that its support is a
butterfly, or that its class-size profile is 3,3,3,3,1,1.

## Sharpness {.unnumbered}

The bound nine is sharp even when adjacent targets are allowed. An explicit
eight-cube counterexample, with a direct Hall proof, is given in
the main article’s direct fifteen-source argument.



# Argument 30: Five opposite cubes and nine adjacent cubes {#arg-30}

## Result {.unnumbered}

**Theorem.** Five opposite-repeat five-colour cubes, with no variety
occurring more than twice, together with nine adjacent-repeat cubes,
with no tricoloured-corner class occurring more than three times, contain
eight cubes that assemble an opposite-repeat target.

This is an elementary proof. Its ingredients are a replacement lemma,
the previously written five-opposite grid constructions, and the
nine-distinct-class theorem. No exhaustive inventory list is used.

The essential new observation is that the third copy of an adjacent
class in the older proofs can be introduced temporarily. All the
subsequent constructions use only two actual copies of that class.

## 1. Replacing the third copy {.unnumbered}

**Replacement lemma.** Let O be any five opposite sources and let A
be an adjacent tricoloured-corner class. If O together with three
copies of A assemble an opposite target, then O together with two
copies of A and any adjacent source B also assemble an opposite
target.

**Proof.** In the given eight-cube assembly, the three A copies occupy
corners on three distinct undirected target edges: an adjacent cut
contains at most one direction of each edge. Every adjacent source
meets an opposite target on at least two underlying edges. Therefore
B has a compatible corner on one of the three edges occupied by A.

If its direction agrees with the A corner, replace that A copy by B.
Otherwise swap the two directed corner positions on that one target
edge. Its other position was occupied by an opposite source, since
the three A positions lie on distinct edges. That opposite source
supports both directions, so it remains compatible. Put B at the
reversed A position and leave the other two A assignments untouched.

This is an operation on the corner assignment. Each chosen source
can then be properly rotated to its assigned corner. It does not
assert a reflection of any physical cube. The repeated colours within
adjacent classes do not affect compatibility with an opposite target.
∎

## 2. The geometric constructions that remain after replacement {.unnumbered}

Fix A=C(01), with its six corners in a two-by-three grid. Colour
permutation and, if necessary, reversal of all directed corners reduce
any adjacent class to this form.

Each opposite variety meets this grid in two positions in different
columns, or in a complete two-column rectangle. Each such pattern
determines its variety uniquely.

If the five opposite sources match four positions of a two-column
rectangle, they assemble with three copies of A: four fill the reverse
rectangle, and the fifth plus the three A copies fill the forward
rectangle. The replacement lemma then gives an assembly with two
actual A copies and any adjacent helper.

Otherwise all three rectangle ranks are at most three. Any five grid
positions contain two complete columns, so a matching to five positions
would give a matching of a complete rectangle. Thus the full grid
rank is at most four. Hall's theorem gives a set H of three or four
grid positions satisfying

    |H| + number of opposite copies with pattern not contained in H ≤ 4.

The elementary consequences of this cover have already been proved
in the five-opposite notes. The relevant conclusions, including the
number of A copies they actually use, are as follows.

### At most one doubled opposite variety {.unnumbered}

The opposite profile is 1,1,1,1,1 or 2,1,1,1. Either all five patterns
lie in a four-position shape with column sizes 2,1,1, or four source
copies lie on three positions in three different columns, with a
fifth outside. In the latter case the four inside copies are 2P+Q+R,
where P,Q,R form a line of neighbouring varieties.

In either case there is a central target T such that:

1. A meets T in exactly two directed corners a,b;
2. after a,b are removed, the five opposite sources can fill any five
   of the remaining six positions.

The proof is the Hall calculation in Sections 1–3 of
[Argument 6](#arg-6).
It uses only the grid cover, not a third physical A cube.

At most two adjacent classes have their entire T-intersection inside
{a,b}. One of those classes is A. Any adjacent helper outside these
at most two classes supplies a third corner c. Use two A copies at
a,b, the helper at c, and the five opposite sources at the remaining
positions.

### Two doubled neighbouring opposite varieties {.unnumbered}

The opposite profile is 2P+2Q+R, with P,Q sharing two undirected
edges. The explicit neighbouring-pairs construction assembles with
two A copies and any helper from a different class. See
[Argument 2](#arg-2).

### Two doubled nonneighbouring opposite varieties {.unnumbered}

Here P,Q share one undirected edge. The grid cover leaves one
overlapping pattern shape or three disjoint pattern shapes. Their
explicit targets and allocations are in Sections 2–3 of
[Argument 5](#arg-5).

Every final construction uses exactly two A copies, all five
opposite sources, and one adjacent helper meeting a specified rescue
set E. In each case at most two adjacent classes avoid E, and A is
one of them. The third A copy occurs only in the initial rectangle
construction already covered by the replacement lemma.

For the overlapping shapes, E consists of five remaining positions
after two A copies and the single opposite source are assigned. The
two opposite pairs fill any four of these five. For the disjoint
shapes, E is the union of the helper positions in two explicit
completions; it consists of two bidirected edges and a further directed
edge joining their components. Keeping both endpoint pairs together
and respecting the remaining direction permits at most two adjacent
cuts. These include A, which has no corner in E.

## 3. A useful nine-cube strengthening {.unnumbered}

The preceding argument proves the following more general statement.

**Helper lemma.** Let A,B,C be three different adjacent
tricoloured-corner classes. Five capped opposite sources, two copies
of A, one source in B, and one in C contain an opposite assembly.
Indeed, at least one of the eight-cube subpools O+2A+B and O+2A+C
assembles.

If O+3A assembles, the replacement lemma applies to either helper.
Otherwise use the grid-cover constructions above. In the low-repetition
and nonneighbouring cases, at most two classes avoid the rescue set,
one of which is A. Thus B and C cannot both avoid it. The neighbouring
case accepts either helper directly. Every construction uses the two
actual copies of A and only one helper. ∎

## 4. Proof of the requested fourteen-cube theorem {.unnumbered}

If the nine adjacent cubes belong to nine different classes, the
elementary nine-distinct-class theorem gives an opposite assembly;
see [Argument 29](#arg-29).

Otherwise some class A occurs at least twice. Since the nine adjacent
sources have class cap three, at least three classes occur. Choose sources from
two other distinct classes B,C. The helper lemma gives an assembly
using the five opposite sources, the two A copies, and one of those
helpers. ∎




# Argument 31: A nonlooped three-copy class has two private corners {#arg-31}

**Theorem.** In a failing pure fourteen-cube pool whose tricoloured
classes have multiplicity at most three, every three-copy class without
a loop has at least two tricoloured corners absent from all other
classes. In fact, it suffices that the class has no loop using its own
cut orientation.

This proof uses the explicit matching lemmas in [Argument 25](#arg-25),
[Argument 26](#arg-26), and [Argument 27](#arg-27). It does not use
the exhaustive lists of fourteen-cube failures.

## 1. Hall covers and four zero cuts {.unnumbered}

Normalize the three-copy class to `A=C(01)`, and suppose at most one
of its six corners is private. Thus its eleven outsiders meet at least
five corners of the two-by-three array `02,03,04;12,13,14`.

Call a cut disjoint from `A` a zero cut. The zero classes are
`B=C(234)` and `Z_i=C({2,3,4}\setminus{i})`, for `i=2,3,4`.

If four zero cubes are present, choose two colours `q,s` each contained
in at least two of their outsets. This is always possible: at most one
of the three `Z_i` multiplicities exceeds two. Their four cubes match
`q0,q1,s0,s1`, since each row has degree at least two and their union
sees all four sources. Some outsider meets the forward half
`{0q,0s,1q,1s}`: otherwise all outsider intersections with `A` would
lie in the other column, contradicting the five-corner hypothesis.
Use that outsider once and three `A` copies for the forward half.
This gives an opposite target. Consequently the zero count satisfies

\[
z\le3.
\]

After removing two `A` cubes for bicoloured corners, one `A` remains.
If the outsiders match five `A` corners, that last `A` completes the
sixth and gives a loop. Their matching rank is therefore at most four.
By Konig's theorem they admit a cover by `c` corner vertices and at
most `4-c` source copies.

* `c=4` with no source exceptions would make at least two corners
  private, contrary to the hypothesis.
* `c=0` leaves at least seven zeros, impossible.
* `c=1` leaves at least eight sources in one singleton-intersection
  class and the zero classes; these have total capacity at most `3+3=6`.

Thus it remains to examine three corners plus one exceptional source,
or two corners plus two exceptional sources.

## 2. The fourth-anchor substitution {.unnumbered}

The following observation allows the four-copy proofs to be reused.
If a cut `R` meets `A` in at least two columns, then for every pair
`q,s` from `{2,3,4}`, it meets the forward half of target `01|qs`.
Hence three `A` and `R` can replace four `A` whenever those four copies
were used to fill that forward half.

The intersections of a cut with `A` are empty, a single cell, a pair
in one row, a two-by-two rectangle, or the full array. Therefore any
exceptional cut contributing at least two new cells has the required
two-column property.

## 3. Three-corner cover, one exceptional source {.unnumbered}

The other ten outsiders have their intersections within three cells.
The exceptional source `R` contributes at least two additional cells,
by the five-corner hypothesis. Up to symmetry the three-cell cover is
a row, a hook, or a disjoint pair-and-singleton.

### Row cover {.unnumbered}

Normalize the row to `02,03,04`. Then `R` contains two corners of the
other row. The ten normal outsiders are exactly the `P_i,D_i` and zero
classes of [Argument 25](#arg-25), now all of capacity three.

The opposite-target arguments in Section 1 of that note still work:
each use of four `A` was a forward half of `01|qs`, so use three `A`
and `R`. Thus `z<=1`. Section 2 is unnecessary, since the class cap
three is already assumed. Section 3 uses only two `A` and reduces the
normal counts to the same Families I and II.

Every completion and conflict in Family I uses at most three `A`, so
its repeated-colour contradiction applies unchanged. In Family II,
the only use of four `A` is to fill the three second-row corners and
one first-row corner in an `A` target. `R` fills one of its second-row
corners and the three `A` fill the other three positions. The same
two looped three-copy classes are therefore joined and require six
different repeated colours. This settles the row cover.

### Hook cover {.unnumbered}

Normalize the cover to `{02,03,12}`. Its nonzero normal classes are

\[
P=C(04),\quad D=C(034),\quad F=C(024),\quad E=C(134).
\]

If `e=0`, the row argument just proved applies. Otherwise
`p+d+f+e+z=10`, with all four counts at most three. The possible
exceptional cuts adding at least two cells outside the hook are

\[
R=C(12),\quad C(013),\quad C(012).
\]

The two-zero and one-zero arguments of the hook proof in
[Argument 26](#arg-26) transfer directly whenever four `A` fill
a target `01|qs`: replace one by `R`. For completeness, the count
reduction is particularly short here. Two zeros already solve by
that matching argument. With one zero, `d>0` gives target `01∣34`;
if `d=0`, then `e=p=f=3`. For zero `Z_3`, target `01∣24` solves;
every other zero supplies `30` in target `02∣13`, whose other seven
positions are `A:03,12`, `E:10,32`, `F:21,23`, `P:01`.

With no zeros, `e>=2` implies `d>0` because the other three counts
could otherwise sum to at most nine. Target `01∣34` then uses the
four-anchor substitution and `E:30,40`, `D:31`, and another
`P,D,F:41`. The only remaining case is `e=1,p=d=f=3`. Its three
possible exceptional sources give these opposite assemblies:

| Exceptional `R` | Target | Assignment |
|---|---|---|
| `C(12)` | `01∣24` | `A:04,12,14`; `P:02`; `R:20`; `F:21`; `E:40`; `D:41` |
| `C(013)` | `13∣24` | `A:12,14`; `D:32`; `R:34`; `F:21,23,41`; `P:43` |
| `C(012)` | `12∣34` | `A:13,14`; `F:23`; `R:24`; `D:31,32,41`; `P:42` |

Thus the hook cover is impossible.

### Disjoint cover {.unnumbered}

Normalize the cover to `{02,03,14}`. Use the same `P,D,F` but now
`E=C(123)`. If `e=0`, use the row case. Otherwise the disjoint-cover
proof in [Argument 26](#arg-26) applies with the fourth-anchor
substitution. Every use of four `A` in that proof fills the forward
half of a target `01|qs`; all other assemblies use at most three `A`.
Its initial half-array lemma also has that forward-half form. All
count bounds remain valid, since the present cap three is stronger
than its cap four. Thus the disjoint cover also gives an assembly.

## 4. Two-corner cover, two exceptional sources {.unnumbered}

There are nine normal outsiders. If either exception adds at most one
cell outside the two-corner cover, add that cell to the corner cover;
there is then a three-corner cover with only one source exception,
already settled. We can therefore suppose both add at least two cells.

### Corners in different rows {.unnumbered}

For a column, normalize to `{02,12}`. The only nonzero normal classes
are `D=C(034), E=C(134)`. Since `d+e+z=9` and each of these three
terms is at most three, all are three. Target `01∣34` needs four
forward sources and `D:31,41`, `E:30,40`. The five-corner hypothesis
guarantees that at least one exception has a forward corner outside
column 2; use it with three `A` to complete the forward half.

For a diagonal, normalize to `{02,13}`. The singleton classes
`D=C(034), E=C(124)` again each occur three times. Target `03∣12`
is filled by `A:02,13`, `D:01,31,32`, `E:10,20,23`.

### Corners in the same row {.unnumbered}

Normalize to `{02,03}`. The normal nonzero classes are
`P=C(04),D=C(034),F=C(024)`, with

\[
p+d+f+z=9,\qquad p,d,f\le3.
\]

Both exceptions `R,S` contain a pair of second-row corners, because
they each add at least two cells outside `{02,03}`. At least one of
`D,F` is present, since otherwise `p+z<=6`. The half-array lemma
with three `A`, the fourth-anchor substitute `R`, a singleton source,
and three zero sources shows that `z<=2`.

The proof now follows the same small conflict clique as in
[Argument 27](#arg-27), with these explicit adjustments:

* `P` has a loop whenever `p,d,f>=2`: reserve two `P`, then use
  `A:02,03`, `D:01,42`, `F:41,43`.
* To join `A` to `P,D`, or `F`, use an `A` target. After reserving
  one cube from each endpoint, two `A` remain. Normal sources fill
  `02,03`; the exceptions fill two different second-row corners,
  possible because each sees two such corners; two `A` finish.
* To join `P,D` or `P,F`, use an `A` target again. Two normal sources
  fill `02,03`; one exception fills a second-row corner and the three
  `A` finish.
* If one of `D,F` occurs three times, their edge is witnessed exactly
  as before: for `f>=3`, reserve one `D,F` and use remaining
  `F:21,23`, `P:01,43`, remaining `D:41`, and `A:03`.

If `z=0`, then `p=d=f=3`; the clique `A,P,D,F`, with `P` looped,
requires `1+3+1+1=6` different repeats. If `z=1`, the counts are a
permutation of `2,3,3`. The same contradiction applies when `p=3`.
When `p=2`, the zero contains 2 or 3, so it loops `F` or `D` as in
the earlier note, and the clique `A,P,F` or `A,P,D` requires
`1+2+3=6` repeats.

If `z=2`, the forward-half argument from that note gives an opposite
assembly unless the two zeros are identical and one of `d,f` is zero.
But then `p+d+f=7` would have only two nonzero counts, contradicting
the cap three. So this final case solves as well.

All possible Hall covers have led to an assembly. The assumed
three-copy nonlooped class must therefore have at least two private
tricoloured corners.



# Argument 32: A source meeting a private corner promotes a triple to an own loop {#arg-32}

**Matching lemma.** In a failing pure fourteen-cube pool with class
multiplicities at most three, suppose a triple class has exactly two
private tricoloured corners. Its other four tricoloured corners can be
matched by four distinct cubes from other classes.

**Promotion corollary.** Adding any cube whose tricoloured corners
include either private corner makes this triple class completable in
its own orientation after two copies are reserved. In particular, an
added opposite-repeat cube meeting a private corner creates an own loop.

## 1. The possible Hall cover {.unnumbered}

Normalize the triple to `A=C(01)`. Its eleven outsiders meet exactly
four of its six tricoloured corners. Call a source disjoint from `A`
a zero source, and write their number as `z`.

There are at most three zero sources. Indeed any four zero cuts have
a matching on two full reverse rows `q0,q1,s0,s1`: choose two rows each
seen by at least two of the sources. Their union sees all four sources.
The corresponding four-corner forward half cannot consist entirely
of private corners, since `A` has only two private corners. An outsider
therefore supplies one forward corner, and three `A` supply the other
three, giving an opposite assembly.

Thus at least eight outsiders meet `A`. Suppose they cannot match its
four nonprivate corners. Their matching rank is at most three, so by
Konig's theorem their incidences have a cover consisting of `c` corner
vertices and at most `3-c` source vertices.

* Three corner vertices and no source exceptions cannot cover four
  occupied corners.
* One corner and two source exceptions cover at most five nonzero
  sources: the unique singleton-intersection class has capacity three.
  Zero corners cover at most three sources.
* Two corners in different rows allow only their two singleton classes,
  with combined capacity six, plus one exception. This is again fewer
  than eight sources.

The only possibility is two corners in one row and one exceptional
source. Normalize these corners to `02,03`. The ordinary nonzero
classes are

\[
P=C(04),\quad D=C(034),\quad F=C(024).
\]

If their counts are `p,d,f`, and the exceptional source is `E`, then

\[
p+d+f+z=10,\qquad p,d,f\le3,\qquad z\le3.
\]

Consequently `1<=z<=3`, and all three ordinary classes are present.
The exceptional source supplies exactly two new `A` corners. It is
therefore one of `C(12),C(13),C(14),C(014)`. In particular, it meets
two second-row columns of `A`, and meets the forward half of every
target `01|qs` with `q,s` in `{2,3,4}`. Thus three `A` and `E` can
fill any such forward half.

## 2. Two or three zero sources give an opposite assembly {.unnumbered}

Choose any two zeros. If they can fill `20,30`, use `F:21,D:31` to
complete the reverse half of target `01|23`.

Otherwise the two zeros must both omit row 2 or both omit row 3:
each zero sees at least one of these rows, and two nonempty neighbour
sets fail a two-position matching only when they are the same singleton.

If both zeros are `C(34)`, let them fill `30,40`, and use `D:31,P:41`
for target `01|34`. If both are `C(24)`, use them at `20,40` and use
`F:21,P:41` for target `01|24`.

In every case three `A` and `E` fill the forward half. Hence `z>=2`
is impossible in a failure.

## 3. One zero source gives a repeated-colour contradiction {.unnumbered}

Now `z=1`, so necessarily `p=d=f=3`.

The class `P` has an own loop. After reserving two `P`, match its
tricoloured corners by

\[
A:02,03;\quad D:01,42;\quad F:41,43.
\]

The zero source contains 2 or 3. If it contains 3, `D` also has an
own loop: after reserving two `D`, use

\[
\text{remaining }D:32;\quad \text{zero}:31;\quad A:02;
\quad P:41,42;\quad F:01.
\]

If the zero contains 2, interchange 2 and 3 to obtain a loop on `F`.

The looped classes `P,D` are joined. If they share a repeated colour,
reserve one of each for an `A` target's bicoloured corners, using pole
0 from `P` and pole 1 from `D`. A remaining `P` fills `02`, an `F`
fills `03`, and `E` fills one second-row corner; three `A` fill the
other positions. The same argument joins `P,F`.

Each looped triple needs three different repeated colours, while the
joined triples must have disjoint repeat sets. Six colours would be
required. This is impossible, completing the matching lemma.

## 4. Promotion by an added source {.unnumbered}

Let the private corners be `u,v`. Reserve two cubes of the triple.
If an added source supplies `u`, use it there, use the remaining cube
of the triple at `v`, and use the four outside matches just proved for
the other corners. This is an own-orientation loop.

If another own-loop triple is already present and its pole pair meets
that of the promoted triple, an assembly follows immediately: both
triples must otherwise use all three possible repeated colours, their
repeat sets overlap, and the universal-restoration argument joins them.
This last conclusion remains valid when the added source is opposite-
repeat; it is used only for a tricoloured position.



# Argument 33: Two own-loop triple classes cannot occur in a failure {#arg-33}

**Theorem.** A failing pure fourteen-cube pool with all tricoloured-class
counts at most three has at most one three-copy class admitting an
own-orientation loop.

An own-orientation loop on a class means that, after removing two copies
of that class, the remaining cubes match its six tricoloured corners.
This proof is elementary and independent of the exploratory own-loop
profile enumeration.

## 1. Repeated colours and the available pole pairs {.unnumbered}

An own-loop triple must use all three possible repeated colours;
otherwise a same-repeat pair completes its own target.

If `U` has an own loop, it conflicts with every present class `V` whose
pole pair meets that of `U`. Indeed, to reserve one `U,V` for an `U`
target, start with the loop matching after two `U` reservations, restore
one universal `U`, and remove the chosen `V`. If the removed `V` had
been used, the restored `U` replaces it.

Consequently two own-loop triples must have disjoint pole pairs. Their
three-element repeat sets overlap, so intersecting pole pairs would
already give a solution. A reverse-orientation class with the same
pole pair as an own-loop triple is absent for the same reason.

Normalize the two pole pairs to `01` and `23`, and the first class to

\[
A=C(01).
\]

The second class is either `C(23)` or `C(014)`. Both triples use all
three repeats: `A` uses `2,3,4`, while the other class uses `0,1,4`.
Every other present pole pair must meet at most one of `01,23`.
If it met both, its repeat would have to lie in both disjoint pairs.
Thus all eight remaining cubes have one of the four pole pairs

\[
04,\quad14,\quad24,\quad34.
\]

Their repeated colours are forced, respectively, to be

\[
1,\quad0,\quad3,\quad2.
\]

## 2. The second class is `C(23)` {.unnumbered}

Consider opposite target `01|23`. Each of the eight possible remaining
classes meets exactly one of its two four-corner halves. If a source
of each kind occurs, use those two sources, three `A`, and three
`C(23)` to fill the target.

Otherwise all remaining sources meet the same half. If they meet the
forward half, their only possible corners in the `C(23)` target are
`24,34`; if they meet the reverse half, their only possible corners in
the `A` target are `04,14`. After reserving two copies of the relevant
anchor, its one remaining universal copy and these two corner positions
cannot supply six corners. One of the asserted own loops is impossible.

Thus this orientation always solves.

## 3. The nested orientation `C=C(014)` {.unnumbered}

Name the eight other classes as follows. A bar denotes the reverse cut.

| Pole pair | Class | Reverse class | Forced repeat |
|---|---|---|---:|
| `04` | `P=C(04)` | `Pbar=C(123)` | 1 |
| `14` | `Q=C(14)` | `Qbar=C(023)` | 0 |
| `24` | `R=C(24)` | `Rbar=C(013)` | 3 |
| `34` | `S=C(34)` | `Sbar=C(012)` | 2 |

Call `P,Q,Rbar,Sbar` the main classes and the other four the outer
classes. Put

\[
a=g(Pbar)+g(Qbar),\qquad b=g(R)+g(S).
\]

### Three preliminary observations {.unnumbered}

**First, `a,b<=3`.** An own-loop triple has at least five tricoloured
corners met by outsiders. Four sources disjoint from it would give an
opposite assembly: choose two reverse rows each met by at least two of
the four zero sources; they fill that reverse rectangle, and some
outsider meets its forward rectangle because the outside support has
at least five of the anchor's six corners. That outsider and three
anchor copies fill the forward rectangle.

The only permitted classes disjoint from `A` are `R,S`, and the only
permitted classes disjoint from `C` are `Pbar,Qbar`. Hence `a,b<=3`.

**Second, a main class of size three excludes every outer source.**
By symmetry it suffices to consider `P^3`. Its two corners outside the
four-corner intersection with `C` are `01,41`. A `Qbar`, `R`, or `S`
supplies one of these. Reserve a same-repeat `P` pair, use its remaining
copy for the other corner, and use three `C` and one `A` for
`02,03,42,43`. This assembles a `P` target.

If a `Pbar` instead occurs, it has the same forced repeat as `P` and
the same poles. Reserve one `P` and one `Pbar`; the two remaining `P`
fill `01,41`, and the same four-corner completion works.

The needed symmetries are interchange of 0 and 1, interchange of 2 and
3, and reversal followed by `(0 2)(1 3)`. The last symmetry exchanges
`A,C`, exchanges the blocks `{P,Q}` and `{Rbar,Sbar}`, and exchanges
the two outer blocks.

**Third, if both main blocks are present, every main count is at most
one.** For example, if `P` occurs twice and `Rbar` occurs, reserve an
`A` cube repeating 3 and that `Rbar` for the poles `04` of a `P` target.
Two `P` fill `01,41`; three `C` and one remaining `A` fill
`02,03,42,43`. The same construction works with `Q`, or with `Sbar`
instead of `Rbar`.

Conversely, if `Rbar` occurs twice and `P` occurs, reserve the `C`
cube repeating 1 and `P` for an `Rbar` target's poles `24`. Two `Rbar`
fill `32,34`; three `A` and one remaining `C` fill
`02,04,12,14`. Again the other choices are symmetric.

### The outer sources have only two types {.unnumbered}

There must be an outer source. If there were none, the own loop on
`A` would require some `Rbar,Sbar`, since its corners `04,14` cannot
both be filled by its one remaining copy. Similarly the own loop on
`C` would require some `P,Q` to supply `42,43`. Both main blocks would
then be present, forcing at most one of each main class, whereas eight
sources are required.

Since an outer source is present, the second observation bounds every
main class by two. If both main blocks occur, the third observation
improves this to one. Either way, the main total is at most four.
Thus

\[
a+b\ge4,\qquad a,b\le3,
\]

so both outer blocks are nonempty.

For target `01|23`, the reverse intersections of the outer classes are

| Class | Reverse positions |
|---|---|
| `Pbar` | `20,30` |
| `Qbar` | `21,31` |
| `R` | `20,21` |
| `S` | `30,31` |

Any three of these four types, with at least four copies in total,
match the four positions. This follows directly from Hall: each
position has a neighbour, any two positions see at least two sources,
and any three positions see every source. Three `A` and one `C`
fill the forward half. Therefore at most two outer types can occur.
Since both outer blocks are nonempty, exactly one occurs in each.
By interchanging 0,1 and 2,3, normalize them to

\[
Pbar^a,\quad R^b,\qquad 1\le a,b\le3,\quad a+b\ge4.
\]

### The remaining numerical cases {.unnumbered}

Write `p,q,rbar,sbar` for the main counts. Their sum is `8-a-b`,
between two and four. By the exchange symmetry above, assume the
block `{Rbar,Sbar}` is present.

If `a>=2` and `sbar>0`, target `04|23` is filled by

\[
A:02;\quad C:03,42,43;\quad Pbar:30,34;\quad
R:20;\quad Sbar:24.
\]

Otherwise consider target `13|24`. Its forward half is filled by

\[
A:12,14;\quad Rbar:32;\quad Pbar:34.
\]

A `C` fills `43`; three `R` can fill its other reverse positions
`21,23,41`. Two `R` also suffice if a `P` supplies `41`.

If `a=1`, then `b=3` and the main total is four. Here `Rbar` must be
present: without it, a single main block has capacity two, while two
present blocks have total capacity at most three. Thus the displayed
target works with three `R`.

The only remaining case has `a>=2` and `sbar=0`, hence `rbar>0`.
If `P,Q` are both absent, the main total is at most two, forcing
`a=b=3`, and three `R` finish. If the block `{P,Q}` is present, every
main count is at most one; therefore `a+b>=5` and `b>=2`. When `b=3`
we again finish with three `R`. When `b=2`, necessarily `a=3` and
`p=q=rbar=1`; use two `R` at `21,23` and the `P` at `41`.

All cases have an opposite or adjacent assembly. Two own-loop triple
classes are therefore impossible in a failure.

## 4. The same exclusion for fifteen cubes {.unnumbered}

The argument also excludes two own-loop triple classes in a failing
pure fifteen-cube pool with class counts at most three. The disjoint-
outset orientation is handled exactly as in Section 2.

For the nested orientation there are now nine star-class helpers.
Every preliminary observation remains valid: `a,b<=3`, an outer
source exists, each main count is at most two, and the main total is
at most four. Consequently `a+b>=5`. The reverse-square argument
again reduces the outer sources to `Pbar^a,R^b`. Now

\[
2\le a,b\le3,\qquad
m=p+q+rbar+sbar=9-a-b\in\{3,4\}.
\]

By the exchange symmetry assume the `Rbar,Sbar` block is present.
If `sbar>0`, the displayed `04|23` assembly applies, since `a>=2`.
Otherwise `rbar>0`. The `P,Q` block cannot be empty, since the main
total is at least three but `rbar<=2`. Both blocks therefore occur,
so each main count is at most one. With `sbar=0`, this forces

\[
m=3,\quad a=b=3,\quad p=q=rbar=1.
\]

The displayed `13|24` assembly, using three `R`, now solves. This
proves the fifteen-cube extension independently of any classification
of fourteen-pools with a unique own-loop triple.



# Argument 34: Adding an opposite source to a butterfly failure {#arg-34}

**Theorem.** Every pool obtained by adding one opposite-repeat cube to
a fourteen-cube butterfly failure has an assembly.

This is an elementary fifteen-cube result. It uses the already proved
butterfly classification and repeated-colour refinement, and does not
require a classification of failures having an own-loop triple.

Normalize the pivot to0 and the two blocks to P={1,2}, Q={3,4}.
The four high classes are

    C1=C(01), C2=C(02), C3=C(124), C4=C(123),

with three cubes in each. The low classes C(12), C(012) occur once.
By the elementary refinement theorem, all three cubes in each high
class have the same repeated colour; the four high repeats form a
derangement of {1,2,3,4}. Both low cubes repeat0.

The private-corner pairs of the high classes are

| Class | Private corners |
|---|---|
| C1 | 02,12 |
| C2 | 01,21 |
| C3 | 40,43 |
| C4 | 30,34 |

If the added opposite source meets one of these pairs, reserve two
same-repeat copies of that high class for its bicoloured corners. Its
third copy fills the other private corner, and the opposite source
fills the chosen private corner. The standard butterfly pools fill
the four remaining positions. For example, for C1, two C2 fill03,04,
while C3 and C4
fill13,14. The other high classes are symmetric.

It remains to consider an opposite source avoiding all eight private
corners. Because an opposite source is symmetric under arc reversal,
it must avoid every undirected edge in the two triangles012 and034.
The only remaining edges are the four between P and Q. Therefore
the unique avoiding opposite variety is O=opposite12|34, omitting0.

For this source assemble the opposite target02|13, omitting4:

    O:32;
    C2:01,21,23;
    C1:03,12;
    C4:10,30.

These are its eight distinct corner types. Hence every opposite source
completes the butterfly failure.




# Argument 35: A common-corner 3,3,2,2 core with a looped triple {#arg-35}

**Lemma.** Suppose four distinct adjacent tricolour classes have a
common directed corner. They occur with multiplicities `3,3,2,2`.
If either of the triple classes admits an own-orientation loop in the
full pool, the full pool is soluble.

An own loop may use any extra sources in the full pool. All other
matchings in this proof use just the ten sources in the stated core.

## 1. Notation and the three possible supports {.unnumbered}

Normalize the common corner to `01`, and put `Q={2,3,4}`. The six
classes containing that corner are

\[
P_i=C(0i),\qquad D_i=C(\{0\}\cup(Q\setminus\{i\})),
\quad i\in Q.
\]

Their pole pairs are `0i` and `1i`, respectively. The symmetries are
arbitrary permutations of `Q`, and interchange of all `P_i,D_i`
(reverse every cut and then interchange colours 0 and 1).

Four present classes leave two absent. Up to these symmetries, the
absent classes are either two `P` classes, `P_i,D_i`, or `P_i,D_j`
with `i!=j`. Consequently it suffices to treat the supports

\[
\{P_4,D_2,D_3,D_4\},\qquad
\{P_3,P_4,D_3,D_4\},\qquad
\{P_3,P_4,D_2,D_4\}.
\]

Recall that a looped triple in a failure must use all three allowed
repeated colours. A looped double uses two distinct repeated colours.
Two classes are called conflicting when a shared repeated colour
would produce an assembly: reserve one cube of each for the two
bicoloured target corners and match the six tricoloured corners.

## 2. Three classes of one kind and one of the other {.unnumbered}

For support `P4,D2,D3,D4`, every pair of classes conflicts already
when all four counts are just two. Here is a complete table. Its
assignments are made after one source of each reserved class is
removed; a class name in the target column specifies its six
tricoloured corners.

| Reserved pair | Target | Tricoloured assignment |
|---|---|---|
| `P4,D2` | `P2` | `P4:03; D2:01; D3:21,23; D4:04,24` |
| `P4,D3` | `P3` | `P4:02; D2:31,32; D3:01; D4:04,34` |
| `P4,D4` | `P4` | `P4:43; D2:02,42; D3:03,41; D4:01` |
| `D2,D3` | `D2` | `P4:02,42; D2:32; D3:41; D4:01,31` |
| `D2,D4` | `D2` | `P4:02,42; D2:32; D3:01,41; D4:31` |
| `D3,D4` | `D3` | `P4:03,43; D2:01,41; D3:23; D4:21` |

In each row the two reserved pole pairs can supply the two poles of
the stated target. Hence these four classes form a conflict clique.
The asserted looped triple needs three repeated colours; each of
the other three classes needs at least one; and all those colours
must be distinct. Six colours would be required, a contradiction.

## 3. Two matched pairs of classes {.unnumbered}

Now the support is `P3,P4,D3,D4`, with all counts at least two and
total ten. We show that these four classes again form a conflict
clique.

The cross pair `P3,D4` conflicts already at counts `2,2,2,2`:
reserve one of each for a `P4` target, and match

\[
P_3:02;\quad D_4:01;\quad P_4:42,43;\quad D_3:03,41.
\]

Interchanging 3 and 4 gives the edge `P4,D3`.

Since the counts total ten, one of

\[
g(P_3)+g(D_4),\qquad g(P_4)+g(D_3)
\]

is at least five. Interchange 3 and 4 if needed, so that the first
sum is at least five. To prove the edges `P3,P4` and `P3,D3`, reserve
one cube of each relevant pair and use target `P3`. Assign

\[
P_3:32;\qquad P_4:02;\qquad D_3:01.
\]

The remaining target positions are `04,31,34`. All remaining `P3`
and `D4` sources contain them, and their number is

\[
g(P_3)-2+g(D_4)\ge3.
\]

Thus they fill the last three positions. The displayed `P4,D3`
sources remain available in either reservation because their
original counts are at least two.

Similarly, to prove `D4,D3` and `D4,P4`, use target `D4`, assigning

\[
D_4:24;\qquad D_3:21;\qquad P_4:01.
\]

Its remaining positions are again `04,31,34`, filled by the remaining
`D4,P3` sources. This gives all six edges. As in Section 2, one
looped triple and the three other nonempty classes would require
six distinct repeated colours. This is impossible.

## 4. Two unmatched absent classes {.unnumbered}

The remaining support is `P3,P4,D2,D4`.

### Two intrinsic loops and four edges {.unnumbered}

At counts `2,2,2,2`, the classes `P3` and `D2` already have own loops.
After reserving two `P3`, match a `P3` target by

\[
P_4:01,02;\quad D_2:31,32;\quad D_4:04,34.
\]

After reserving two `D2`, match a `D2` target by

\[
P_3:02,32;\quad P_4:41,42;\quad D_4:01,31.
\]

The usual universal-restoration argument therefore gives the edges
`P3,P4` and `D2,D4`, since the corresponding pole pairs intersect.
Two more edges have the following explicit matchings:

| Reserved pair | Target | Tricoloured assignment |
|---|---|---|
| `P3,D4` | `P4` | `D4:01; P3:02; D2:41,42; P4:03,43` |
| `P4,D2` | `D4` | `P4:01; D2:31; P3:04,34; D4:21,24` |

If `P4` has count three, then `P4,D4` also conflict: reserve one
of each for target `P4`, and assign

\[
P_4:03,43;\quad D_2:41,42;\quad P_3:02;\quad D_4:01.
\]

If `D4` has count three instead, use target `D4`, with

\[
D_4:21,24;\quad P_3:04,34;\quad D_2:31;\quad P_4:01.
\]

### Neither intrinsic-loop class can be a triple {.unnumbered}

Suppose `P3` is a triple. Its loop forces its repeated-colour set to
be `{1,2,4}`. Its conflict with `P4`, whose poles are `04`, then
forces every `P4` to repeat 3.

The looped class `D2` has allowed repeats `{0,3,4}` and conflicts
with `P4`. It therefore cannot be a triple, and its two copies must
repeat 0 and 4. A `D4` must avoid the repeat sets of both `P3` and
`D2`, by the two edges above. Since its allowed repeats are
`{0,2,3}`, it too must repeat 3.

The second triple is now either `P4` or `D4`. The corresponding
displayed matching gives the edge between them. Both repeat 3, a
contradiction.

The symmetry interchanging all `P,D` classes and then interchanging
2 and 3 exchanges `P3` and `D2`, while preserving this support. It
excludes a `D2` triple in the same way.

### The remaining two triples {.unnumbered}

Consequently `P3,D2` are the doubled classes and `P4,D4` are the
triples. At least one of these latter two is assumed to have an own
loop in the full pool.

If `P4` is looped, it uses all repeats `{1,2,3}`. Its conflict with
the looped double `P3`, whose repeats must be two distinct members
of `{1,2,4}`, leaves only 4 available to `P3`. This is impossible.

If `D4` is looped, it uses all repeats `{0,2,3}`. Its conflict with
the looped double `D2`, whose repeats must be two distinct members
of `{0,3,4}`, again leaves only 4. This is equally impossible.

All three support cases have been exhausted by the two-absence
classification in Section 1. The lemma follows.



# Argument 36: No triple in a failing pure fourteen-pool has a private row pair {#arg-36}

**Lemma.** Consider a failing pool of fourteen adjacent-repeat cubes,
with every tricoloured class of multiplicity at most three. No triple
class has two private corners in one row of its two-by-three cut array.
Consequently every triple without an own-orientation loop has exactly
two private corners.

The dependencies are the nonprivate-triple lemma
[Argument 31](#arg-31), the two-own-loop exclusion
[Argument 33](#arg-33), the six-repeated-class bound
[Argument 28](#arg-28), and the common-corner lemmas
cited below. None uses this row-pair exclusion.

## 1. Row geometry {.unnumbered}

Normalize the distinguished class to A=C(01), with private corners
02 and03, and put Q={2,3,4}. Every outsider avoids both private corners.
The possible outsider classes are exactly

    P_i=C(1i), N_i=C(1,Q\{i})  (i∈Q),
    H=C(023), B=C(234), Z_i=C(Q\{i})  (i∈Q).

The six P/N classes have the common corner 10. Write v for their total
multiplicity, h for the H multiplicity, and z for the total B/Z
multiplicity. Thus v+h+z=11, with every individual class count at most3.

In the reverse-A array, whose rows are q0,q1 for q∈Q, the P/N sources
meet only the 0-column:

    P_i sees i0;       N_i sees j0,k0.

Their intersections with A are complementary sets of columns in the
1-row: P_i sees 1j,1k, while N_i sees1i. A B/Z source sees both
positions in at least two reverse rows. H sees21,31 and no 0-column
position. Thus every source outside the P/N family that meets the
reverse 1-column meets at least two rows there.

### At most three zero-intersection sources {.unnumbered}

Suppose z≥4 and some nonzero-intersection outsider is present. If z≥5,
every reverse row sees at least z−3≥2 zero sources. Choose a two-row
rectangle containing a forward column met by a nonzero outsider X.
Four zero sources fill the reverse half: each row has degree at least2,
and every zero source meets their union. X and three A fill the forward
half.

If z=4, choose two reverse rows each having zero-source degree at least2.
At most one row can fail this bound. The seven nonzero outsiders cannot
all meet A in the remaining column: only the two singleton-intersection
classes for that column could do so, with total capacity6. Thus an X
meeting the chosen rectangle exists, and the same construction works.

If every outsider is zero, z=11. The three Z classes have capacity9,
so B is present; their combined count is at least8 because B≤3.
The Z sources alone match all six corners of reverse A: every row has
at least five neighbours and any two rows see all Z sources. A repeated
colour among the three A copies would therefore solve the reverse-A
target. Otherwise A uses all three possible repeat colours, and any B
copy shares one of them; one A and that B supply the bicoloured corners,
while the Z sources fill the tricoloured corners. This also solves.

Consequently z≤3.

### Reducing to two exceptional supports {.unnumbered}

Put u=h+z. Suppose u≥2. Then u≤6 and v=11−u≥5. Let R⊆Q be the
rows met by the P/N sources in the reverse 0-column. Since only P_i is
confined to a single row and its count is at most3, |R|≥2.

We first record a small completion fact. If i,j∈R, three distinct P/N
sources can fill i0,j0 and one forward corner of the rectangle on i,j.
To apply Hall, regard the last position as a flexible slot accepting
any source with either1i or1j. Its degree is v−n_k≥2, where k is the
third row. The first two positions have positive degree, and their
union has degree v−p_k≥2. The flexible slot together with either
0-column position sees every P/N source, by the complementary pattern
in Section1. Thus Hall holds. Three A fill the other forward positions.

If the u sources can match two distinct reverse 1-column positions
whose rows lie in R, the preceding completion gives an opposite target.
For |R|=3 they always can. For R={i,j}, every such source meets at
least one of these rows, and u≥2, so failure forces all of them to
miss one row, say j.

All zero sources are then Z_j, and H can occur only if j=4. Every one
of these u sources meets rows i,k, where k is outside R. If z>0 and
u≥3, use a Z_j at k0 and two other u-sources at i1,k1. Two distinct
P/N sources supply i0 and one forward corner of the i,k rectangle:
the former has positive degree, the latter has degree v−n_j≥2, and
their union contains all v sources. Three A complete the forward half.

There remain just two possibilities.

* u=2. Then v=9. Because the 0-column support is R={i,j}, the only
  possible P/N classes are P_i,P_j,N_k, so each has count3.
* z=0 and h≥2. Then j=4, v=11−h≥8, and the same three classes
  P_i,P_j,N_k are the only possibilities. All are present, and at
  least one of P_i,P_j has count3.


## 2. The two exceptions need no all-private assumption {.unnumbered}

Whenever `A,P_i,P_j,N_k` are present, both `P_i` and `P_j` have
at most one private corner. For `P_i`, A covers its 1-row corners,
`P_j` covers `10`, and `N_k` covers `i0,ik`, leaving at most `ij`.
The statement for `P_j` is symmetric. The nonprivate-triple lemma
therefore makes either of these classes an own-loop class if its
count is three.

The first exception has two such triples. It contradicts the
two-own-loop-triple exclusion.

In the second exception, `h=2` likewise makes all three common
classes triples, giving the same contradiction. Thus `h=3` and
their counts sum to eight. If both `P_i,P_4` are triples, again
there are two own-loop triples. Otherwise `N_k` is a triple and
exactly one of `P_i,P_4` is a triple, with the other doubled.

If `P_4` is that triple, its own loop conflicts with the present
class `H=C(023)`, which has the same pole pair `14`. The looped
triple uses all three allowed repeated colours; H has no other
allowed repeated colour. This is impossible.

If `P_i` is the triple, its own loop uses all three repeated
colours outside its poles `1i`. Both A and H have pole pairs
meeting `1i`, so own-loop restoration makes them conflict with
`P_i`. Each A and each H must consequently repeat `i`.
Reserve one A and one H for an A target's bicoloured corners.
Its six tricoloured corners have the completion

\[
 A:02,03;\qquad H:04;\qquad P_4:1i;\qquad
 N_k:1k;\qquad P_i:14.
\]

All six sources remain available: A and H originally have three
copies each, and the other three classes are present. This is a
solution, another contradiction.

Thus `u<=1`, and hence `v>=10`.

## 3. Ten common-corner sources are now impossible {.unnumbered}

If all six P/N classes occur, the common-corner nine-cube theorem
applies. At most three present classes have capacity at most nine.
It remains to consider four or five present common-corner classes.

With five classes present, every one has at most one private
corner even within this family. Thus every triple among them has
an own loop, and at most one can be a triple. Their total is at
most eleven.

If the total is eleven, the counts are `3,2,2,2,2`; these five
repeated classes, together with A, violate the six-repeated-class
bound. If the total is ten and there is no triple, all five are
doubled, giving the same contradiction. The only remaining
profile is `3,2,2,2,1`, which always solves by
[Argument 23](#arg-23).

With exactly four common-corner classes present, at most one has
two private corners after A is included. Here is the two-absence check. In the common-corner family,
P_i has private arcs $i\to j,i\to k$ only when $N_j,N_k$ are
absent; if only $N_j$ is absent, a second private arc $1\to j$
also requires $P_k$ absent. The dual statements hold for N_i.
The additional class A supplies every $1\to q$, removing that
second P-type arc. If both absent classes are N-types, only the
complementary P-type can retain two private corners; the dual holds
when both are P-types. With one absent type of each kind, at most
one N-type retains two. Hence at most one triple can lack an
own loop. Since there is at most one own-loop triple as well,
the total is at most `3+3+2+2=10`.

Equality is required by `v>=10`. The profile is therefore
`3,3,2,2`, and at least one of its two triples has an own loop.
The lemma [Argument 35](#arg-35)
excludes exactly this case.

All possibilities have been excluded, proving the row-pair lemma.

## 4. Consequence for every non-own-loop triple {.unnumbered}

The nonprivate-triple lemma gives at least two private corners
to every triple without an own loop. Three private corners in
a two-row array would put two in one row, which has just been
excluded. Thus such a triple has exactly two private corners.

In particular [Argument 32](#arg-32) now applies to
every non-own-loop triple in a failing pure fourteen-pool: its
four nonprivate corners have an outsider matching, and adjoining
any source meeting a private corner creates an own loop.



# Argument 37: Every non-own-loop triple has a private column {#arg-37}

**Lemma.** In a failing pool of fourteen adjacent-repeat cubes, with
all tricoloured class counts at most three, every triple without an
own-orientation loop has exactly two private corners, in one column
of its two-by-three cut array.

The unconditional row lemma already gives exactly two private corners.
Here we exclude a diagonal pair even when the pool has one own-loop
triple. The proof uses [Argument 36](#arg-36), the
nonprivate-triple lemma, and the two-own-loop-triple exclusion.

**Orientation convention.** For a positive class `C(pq)`, a row pair
has the same tail `p` or `q`. For a negative class `C(V\{p,q})`, a
row pair has the same head `p` or `q`. In particular the pairs
`40,42` in `C(134)` and `20,24` in `C(123)` are column pairs; we
make no row-based exclusion of them. 

## 1. The diagonal normal form and reverse rectangles {.unnumbered}

Normalize the distinguished triple to `A=C(01)` with private
corners `02,13`. Its eleven outsiders avoid these corners, and
have exactly the following possible classes:

\[
\begin{array}{lll}
X_0=C(13),&X_1=C(134),&X_2=C(123),\\
Y_0=C(02),&Y_1=C(024),&Y_2=C(023),
\end{array}
\]

together with `B=C(234)`, `Z_2=C(34)`, `Z_3=C(24)`, and
`Z_4=C(23)`. Let `x_i,y_i` be their counts, `x=Σx_i`, `y=Σy_i`,
and let `z` count the B/Z sources. Thus `x+y+z=11`.

A has exactly two private corners, so its other four corners are
covered by outsiders; in particular `x,y>0`. The reverse-A
intersections are as follows.

| Class | Reverse-A corners |
|---|---|
| `X_0` | `30` |
| `X_1` | `30,40` |
| `X_2` | `20,30` |
| `Y_0` | `21` |
| `Y_1` | `21,41` |
| `Y_2` | `21,31` |

Each B/Z source sees both reverse corners in at least two rows.

A matching of four outsiders to any reverse rectangle
`q0,q1,s0,s1` implies an opposite assembly. To verify Hall, a set of at
most three target corners meeting A has its three copies as neighbours.
A four-set meeting A gains an outsider from the reverse matching if it
meets the reverse half; otherwise A has only two private corners, so
the forward four-set also gains an outsider. Reverse-only sets are
covered by the assumed matching. For five- and six-sets, their complements
contain complete intersections of at most three and two adjacent classes,
respectively. The class cap gives at least $14-9=5$ and $14-6=8$
neighbours. A complement of at most one corner contains no whole source
intersection. These are all Hall inequalities.

It follows that `z<=3`. At `z>=5` each reverse row has at least
`z-3>=2` zero neighbours; at `z=4` some two rows each have degree
at least two. In either case four zeros match a reverse rectangle.

The permutation `(0 1)(2 3)` exchanges X and Y and exchanges
`Z_2,Z_3`. We will use this symmetry.

## 2. Preliminary restrictions if the base class is a triple {.unnumbered}

Suppose `x_0=3` and at least one of `x_1,x_2` is positive. A and
that branch cover all but at most one corner of `X_0`, so the
nonprivate-triple lemma gives `X_0` an own loop.

Its three cubes must use all three repeated colours outside its
pole pair `13`. Its reverse class `Y_1=C(024)` is therefore absent:
own-loop restoration makes classes with the same poles conflict,
and `Y_1` has the same three available repeated colours. Thus

\[
y_1=0.
\]

If `Y_0,Y_2` both occur, neither can be a triple. A and `Y_2`
cover all but corner `23` of `Y_0`, while `Y_0` and `X_0`
cover all but corner `31` of `Y_2`. A triple in either class
would have another own loop. Since at most one own-loop triple
is possible, both counts are at most two. If only one class is
present, its count is at most three. Consequently

\[
y\le4.
\]

Also `x_2<=2`. Indeed `X_0` covers four corners of `X_2`,
leaving only `20,24`. At least one of `Y_0,Y_2` occurs because
`y>0` and `y_1=0`; either covers `24`. Thus a triple `X_2`
would have at most one private corner and give a second own loop.
We have proved

\[
x_0=3,\quad x_2\le2,\quad x\le8,\quad
 y_1=0,\quad y\le4.
\]

## 3. The base-triple exception is impossible {.unnumbered}

Continue under the assumptions of Section 2.

### No zero sources {.unnumbered}

Now `x+y=11`, so `x>=7` and `y>=3`. In particular `x_2>0`.
If `y_2>0`, match rectangle 2,3 by

\[
X_2:20;\quad X_0:30;\quad Y_2:31;\quad
\text{another Y}:21.
\]

Thus `y_2=0`, giving `y=y_0<=3`. Equality is forced, as is
`x=8`, and therefore

\[
x_1=3,\qquad x_2=2,\qquad y_0=3.
\]

But `Y_0=C(02)` then has private corners `21,23`: none of
A or the X classes contains either. They form a private row pair
in this positive class, contradicting the unconditional row lemma.

### One zero source {.unnumbered}

Here `x+y=10`, so `x>=6` and `y>=2`.

If the zero is B or `Z_4`, an `X_2` gives rectangle 2,3 by
`X_2:20, X_0:30, Y:21, zero:31`; a `Y_2` gives the analogous
rectangle using zero `20`, `X_0:30`, and another Y at `21`.
Thus `x_2=y_2=0`. But then `x<=6` and `y=y_0<=3`,
contradicting their sum ten.

If the zero is `Z_2`, the first of those constructions gives
`x_2=0`. Hence `x<=6` and `y>=4`; equality is forced, so
`x_1=3` and `y_0=y_2=2`. Rectangle 3,4 is filled by
`X_1:40, X_0:30, Y_2:31, zero:41`.

If the zero is `Z_3`, a `Y_2` gives rectangle 2,3 by
`zero:20, X_0:30, Y_2:31`, and another Y at `21`.
Thus `y_2=0`, so `y<=3` and `x>=7`. Both X branches occur.
Rectangle 2,4 is filled by
`X_2:20, X_1:40, Y_0:21, zero:41`.

### Two or three zero sources {.unnumbered}

If two zeros match `20,31`, an X at `30` and a Y at `21`
finish rectangle 2,3. Every zero sees at least one of `20,31`;
with at least two copies, failure of this two-position matching
means that they all miss row 2 or all miss row 3. Thus they are
all `Z_2`, or all `Z_3`.

Both types see `40,41`. Two zeros at those positions, together
with `X_2:20` and a Y at `21`, exclude `x_2>0`. Similarly
using `X_0:30,Y_2:31` excludes `y_2>0`. Hence `x_2=y_2=0`.
The equation `3+x_1+y_0=11-z>=8` forces `x_1>=2`.

For zeros all `Z_2`, match rectangle 3,4 by
`X_1:40, X_0:30`, and two zeros at `31,41`.
For zeros all `Z_3`, match rectangle 2,4 by
`X_1:40, Y_0:21`, and two zeros at `20,41`.
Both give a contradiction.

This proves that `x_0=3` is impossible whenever either X branch
is present. By symmetry, `y_0=3` is impossible whenever either Y
branch is present.

## 4. The original count bounds are restored {.unnumbered}

We now have

\[
x_0\le2\text{ if }x_1+x_2>0,
\qquad y_0\le2\text{ if }y_1+y_2>0.
\]

Therefore `x,y<=8`; if either branch of a group is absent,
that group's total is at most five. These are the count bounds
used in the original diagonal proof, now established without
an all-private hypothesis. We finish its three zero-count cases,
replacing its final private-corner objections where necessary.

## 5. No zero sources {.unnumbered}

Here `x+y=11`, so `x,y>=3`. If `x_2,y_2>0`, match rectangle
2,3 by `X_2:20`, another X at `30`, `Y_2:31`, and another
Y at `21`. By symmetry suppose `x_2=0`.

Then `x<=5` and `y>=6`, forcing `y_1,y_2>0`. An `X_1`
would give rectangle 3,4 using `X_1:40`, another X at `30`,
`Y_2:31,Y_1:41`. Thus `x_1=0`. The counts now force

\[
x_0=3,\qquad y_0=2,\qquad y_1=y_2=3.
\]

The positive class `X_0=C(13)` has private corners `30,32`:
A and all three Y classes miss both. This is a forbidden private
row pair. Hence there are no zero-free failures of this form.

## 6. Two or three zero sources {.unnumbered}

As in Section 3, the `20,31` test forces all zeros to be one
of `Z_2,Z_3`. By symmetry choose `Z_2`.

Two zeros at `40,41` exclude `x_2>0` using rectangle 2,4,
and exclude `y_2>0` using rectangle 3,4. Thus `x_2=y_2=0`.
Now `x,y<=5` and `x+y=11-z` is eight or nine, so `x,y>=3`.
If `x_1,y_1>0`, rectangle 3,4 is supplied by `X_1:40`,
another X at `30`, `Y_1:41`, and a zero at `31`.

If `x_1=0`, the counts force `z=3`, `x_0=3`, and `y=5`.
But the positive class `Z_2=C(34)` has private corners `40,42`,
since A, `X_0,Y_0,Y_1` all miss both. Its three copies have a
forbidden private row pair.

If `y_1=0`, the counts force `z=3`, `y_0=3`, and `x=5`.
Now the positive class `Y_0=C(02)` has private corners
`21,23,24`, all missed by A, `X_0,X_1,Z_2`. Again a triple
has a forbidden private row pair.

## 7. One zero source {.unnumbered}

Now `x+y=10`, so `x,y>=2`.

If the zero is B or `Z_4`, it sees both rows 2,3. An `X_2`
gives rectangle 2,3 with another X, a Y, and zero `31`; a
`Y_2` gives the symmetric construction. Thus `x_2=y_2=0`,
forcing `x=y=5`. In particular both `X_1,Y_1` occur, and
rectangle 3,4 is matched by `X_1:40`, another X at `30`,
`Y_1:41`, and zero `31`.

Otherwise symmetry makes the zero `Z_2`. An `X_2` again gives
rectangle 2,3, so `x_2=0`, `x<=5`, and `y>=5`. If `y_1,y_2`
are both positive, match rectangle 3,4 by `X:30`, zero `40`,
`Y_2:31,Y_1:41`. Therefore one Y branch is absent, and the
bounds give

\[
x_0=2,\quad x_1=3,\quad y_0=2,
\]

with exactly one of `y_1,y_2` equal to three.

If `y_1=3`, use `X_1:40`, another X at `30`, `Y_1:41`,
and zero `31` for rectangle 3,4.

If `y_2=3`, neither `X_1` nor `Y_2` has any private corner.
For `X_1`, `X_0` covers `10,12,30,32` and `Z_2` covers
`40,42`. For `Y_2`, `Y_0` covers `01,04,21,24`, `Z_2`
covers `31`, and `X_0` covers `34`. The nonprivate-triple
lemma gives both triples own loops, contradicting the
at-most-one-own-loop theorem.

All cases have now been excluded. A non-own-loop triple cannot
have a diagonal private pair. Its two private corners therefore
form a column, as claimed.



# Argument 38: Private columns force a butterfly {#arg-38}

**Theorem.** Let a failing pool consist of fourteen adjacent-repeat cubes.
Suppose no class of multiplicity three is completable in its own
orientation after two copies have been reserved. Then the pool is
contained in a butterfly support family. Consequently the earlier
butterfly classification gives the class-size profile `3,3,3,3,1,1`.

This is a hand argument, using the already proved facts that a pure
fourteen-failure has maximum class size three, has at most five repeated
classes, and that, under the present hypothesis, each triple class has
exactly two private corners in a column. The stronger private-column lemma in
[Argument 37](#arg-37) proves this
without assuming that the other triples lack own completions.

Here `ab` means the directed corner a→b, and C(S) is the directed cut
S→Sᶜ on the five colours. A private corner of a class belongs to no
other occupied class. A butterfly support family has no supported
opposite target; the elementary classification of such families is
in [Argument 15](#arg-15).

## 1. Normalize one triple class {.unnumbered}

Choose a triple class and, reversing all cuts if necessary, normalize it
to A=C(01), with private column {02,12}. Every other outset must satisfy

    0∈S ⇒ 2∈S,        1∈S ⇒ 2∈S.

The complete list of possible other classes, and their intersections
with the reverse-A array, is:

| Name | Class | Reverse-A corners |
| --- | --- | --- |
| P | C02 | 21 |
| Q | C12 | 20 |
| L3 | C123 | 20,30 |
| L4 | C124 | 20,40 |
| R3 | C023 | 21,31 |
| R4 | C024 | 21,41 |
| H | C012 | none |
| B | C234 | 20,21,30,31,40,41 |
| Z23 | C23 | 20,21,30,31 |
| Z24 | C24 | 20,21,40,41 |
| Z34 | C34 | 30,31,40,41 |

The reverse array has rows {20,21}, {30,31}, {40,41}. Call B and the
three Z classes the zero classes: they have no tricoloured corner in A.
Lower-case letters denote the corresponding multiplicities.

We use the following completion observation throughout.

**Reverse-rectangle criterion.** If four outsiders match both reverse
corners in each of two rows, the pool has an opposite assembly.

Indeed use the opposite target whose forward half is the corresponding
four corners of A. Hall holds for a set of at most three corners meeting
the forward half, because the three A copies meet it. For a four-set
meeting both halves, the A copies and a reverse neighbour suffice. For
the whole forward half, an outsider neighbour exists because A has only
two private corners. Sets contained in the reverse half are covered by
the assumed four-corner matching. Finally a complement of three corners
contains entire intersections with at most three adjacent classes, and
a complement of two contains at most two. The class cap three therefore
gives at least 14−9=5 neighbours to a five-set and at least 14−6=8 to
a six-set. Every adjacent class meets an opposite target in at least
two corners, so seven- and eight-sets see all fourteen sources. These
are all Hall inequalities.

## 2. Three classes cannot be triples {.unnumbered}

### H has at most two copies {.unnumbered}

A covers four of H's six corners, leaving only {23,24} as possible
private corners. If H were a triple, both would be private. Avoiding
{02,12,23,24} leaves only A,B,Z34 besides H. Four classes with cap
three contain at most twelve cubes. Thus h≤2.

### B has at most two copies {.unnumbered}

Suppose A and B each have three copies. For any opposite target with
parts 01 and two of {2,3,4}, they supply three universal forward and
three universal reverse sources. Two additional sources, one at a
forward corner and one at a reverse corner, complete the target.

If a helper has a corner in both halves, any second helper allows
this completion: every adjacent class meets the target, and the first
helper can take the opposite half from the second. Each of P,Q,L3,L4,
R3,R4 has such a mixed intersection for some target through A. For P,Q
use rows 2,3; for L3,R3 use rows 2,4; for L4,R4 use rows 2,3. Thus none
of these classes can occur.

The eight helpers must therefore lie in H and the Z classes. H meets
only the forward half of every target through A, and every Z meets only
the reverse half. Both kinds occurring would complete a target. If all
helpers are H, B has all six corners private; if all are Z classes, A
has all six private. Both contradict the private-column hypothesis.
Therefore b≤2.

### Z34 has at most two copies {.unnumbered}

Suppose A and Z34 are triples, and use target 01∣34. They supply the
two universal halves. Each L/R helper meets both halves and would
complete the target with any second helper. The remaining helpers split
into forward-only classes P,Q,H and reverse-only classes B,Z23,Z24.
Both kinds occurring again complete the target. If all helpers are
forward-only, every corner of Z34 is private. If all are reverse-only,
every corner of A is private. Thus z34≤2.

## 3. A second triple must exist {.unnumbered}

Suppose every class other than A has multiplicity at most two. Since
h≤2, at least nine outsiders have a nonempty reverse-A intersection.

Their matching rank on the six reverse corners is at most four. A
matching of size five would occupy two full rows, and the reverse-
rectangle criterion would solve the pool.

By König's theorem, cover these incidences by at most four vertices,
of which c are corner vertices and at most 4−c are physical-source
vertices. Every nonexceptional source has its whole reverse pattern
inside those c corners.

For c≤3, at most c distinct nonempty patterns fit inside the chosen
corners. To see this without a case table, the six patterns of size at
most two form two disjoint rooted stars, each with its root singleton:
root20 with leaves30,40, and root21 with leaves31,41. Within each star,
the number of contained patterns is at most the number of selected
vertices. Every other nonempty pattern has size at least four. Each
pattern has multiplicity at most two, so at most
2c+(4−c)=4+c≤7 nonempty sources can occur, a contradiction.

For c=4 there are no source exceptions. At least five distinct patterns
must fit inside the four corners, since at least nine sources occur.
The only four-corner sets containing five listed patterns are rows 2,3
or rows 2,4 in full. Their five patterns are P,Q,Lq,Rq,Z2q, respectively.
Every one must occur, since four patterns have capacity only eight.
The four classes P,Q,Lq,Rq match 21,20,q0,q1. This is a reverse
rectangle, another contradiction.

Thus some class besides A has multiplicity three.

## 4. A triple P or Q forces butterfly support {.unnumbered}

By symmetry it suffices to treat P. Since A supplies P's corners 03,04,
the only possible private column of P is {01,21}. Avoiding this pair
as well as {02,12} leaves only

    A, P, Q, L3, L4, Z34, H.

If Q were also a triple, its private column would be {10,20}, excluding
L3,L4. Then the pool has at most 3+3+3+2+2=13 cubes, using the bounds
on Z34,H. Thus q≤2.

Suppose z34>0. Neither L3 nor L4 can be a triple: A rules out its
column indexed 1, P rules out its column indexed 2, and Z34 rules out
its remaining column. Therefore q,l3,l4,z34,h≤2 and

    q+l3+l4+z34+h=8.

At least one of L3,L4 occurs; by symmetry take L3. Since
q+l3+l4≥4, match reverse corners by

    L3:30; Z34:31; P:21;
    another source from Q,L3,L4:20.

The reverse-rectangle criterion gives a contradiction. Consequently
z34=0, and all sources lie in

    {C01,C02,C12,C123,C124,C012}.                 (F)

This is a butterfly family: its union misses exactly 31,32,41,42.

The same argument with colours 0,1 exchanged handles Q and gives the
reflected butterfly family with R3,R4 in place of L3,L4.

## 5. Any triple L/R class forces butterfly support {.unnumbered}

The symmetries 0↔1 and 3↔4 reduce this to L3=C123.

A rules out L3's column indexed 1. Its column indexed 2 is {20,24};
if this were private, the only other allowed classes would be A,R4,Z34,
whose combined capacity with L3 is at most twelve. Thus L3's private
column is {30,34}. The possible sources are now exactly

    A, L3, P, Q, L4, R4, Z24, H.

If P is a triple, Section 4 already gives (F). If L4 is a triple, the
same private-column argument forces its pair {40,43}; this excludes
R4,Z24 and directly gives (F).

R4 cannot be a triple, since the following eight-source assignment
assembles target 04∣13:

| Sources | Corners |
| --- | --- |
| 2 A | 03,14 |
| 3 L3 | 10,30,34 |
| 3 R4 | 01,41,43 |

Q cannot be a triple: its only possible private column is {10,20},
already supplied by L3. We may therefore assume

    p,q,l4,r4,h≤2.

We next show z24≤2. If Z24 were a triple, its column indexed 0 is
blocked by L3 at 20. Its column indexed 3 is {23,43}; making this
private leaves only A,L3,Z24, far too few sources. Therefore its
private pair would be {21,41}, excluding P,R4. This forces

    q+l4+h=5,

so l4>0. But then L3:20, L4:40 and two Z24 at21,41 form a reverse
rectangle. Thus z24≤2 as claimed.

All six counts p,q,l4,r4,z24,h are now at most two and total eight.
Put

    R=p+l4+r4+z24=8−q−h≥4.

To fill reverse rows 2,4, use an L3 at20 and seek a matching on
{21,40,41}. The relevant neighbour patterns are

| Class | Positions |
| --- | --- |
| P | 21 |
| L4 | 40 |
| R4 | 21,41 |
| Z24 | 21,40,41 |

Every pair has at least two neighbours: for {40,41}, subtract p≤2
from R≥4; for {21,41}, subtract l4≤2; the other pair sees all R.
The three-set sees R≥4. Also 21 has at least R−l4≥2 neighbours.
Thus Hall can fail only if 40 or 41 is unsupported, namely

    l4+z24=0  or  r4+z24=0.

Hence z24=0. If r4=0, all sources lie in (F). Otherwise l4=0, and
R=p+r4≥4 forces p=r4=2. The total then gives q=h=2. Together with
A,L3, these are six repeated classes, forbidden by the six-repeated-
classes theorem. This proves the claim for every L/R triple.

In particular the conclusion of Sections 4 and 5 excludes every zero
class whenever one of P,Q,L3,L4,R3,R4 is a triple.

## 6. The remaining zero classes cannot be triples {.unnumbered}

It remains to consider Z23,Z24; exchange 3,4 to treat Z23.

If Z23's private column is indexed 4, its pair is {24,34}. The only
other allowed classes are A,B,L4,R4,Z24,Z34. None supplies 04 or14.
These would be additional private corners of A, contradicting that
A has exactly the pair {02,12}.

If Z23's private column is indexed 0, its pair is {20,30}. The only
other allowed classes are A,P,R3,R4,H. A triple among P,R3,R4 would
force butterfly support by Sections 4 or 5, excluding Z23. Thus all
four of P,R3,R4,H have counts at most two. Their total must be eight,
so all are doubled. Together with A,Z23, this is again six repeated
classes, impossible.

The column indexed 1 is the same argument with 0,1 exchanged.
Therefore Z23,Z24 are not triples.

## 7. Conclusion {.unnumbered}

Section 3 forces a second triple. Sections 2 and 6 exclude H,B and all
Z classes as that triple. It must therefore be P,Q or an L/R class,
and Sections 4 and 5 force a butterfly support family.

The earlier elementary butterfly classification now gives exactly four
triple classes and two singleton classes. In particular, for this entire
branch,

    A_stat = 4 binom(3,2)=12,    B_stat=0,    3A_stat−4B_stat=36.

This closes the all-private pure branch. It does not settle a pool with
an own-orientation looped triple; that is a separate remaining branch.



# Argument 39: An elementary sharp threshold for adjacent-repeat cubes {#arg-39}

**Theorem.** Any fifteen adjacent-repeat five-colour cubes contain eight
that assemble a five-colour 2×2×2 cube with monochromatic faces. Fourteen
do not suffice.

This proof does not use the exhaustive fourteen-cube failure list. It
also does not require finishing the classification of fourteen-failures
with exactly one own-orientation looped triple. It is a synthesis of the
written elementary lemmas indexed below; the full proof chain is longer
than this final deletion argument.

## 1. Three established facts {.unnumbered}

A tricoloured-corner class consists of three adjacent-repeat varieties
with the same six oriented tricoloured corners. Call a class *own-looped*
if, after two cubes from it are reserved, the remaining pool matches its
six tricoloured corners. The property is monotone under adding cubes.

The following results have elementary proofs.

1. **Concentration and diversity bounds.** A failing pure fourteen-pool
   has maximum class size three; a pool occupying nine distinct classes
   already has an opposite assembly; a pure fourteen-pool with six
   repeated classes assembles.
2. **No own-looped triple.** A pure fourteen-failure with no own-looped
   triple lies in a butterfly family and has class counts3,3,3,3,1,1.
3. **Two own-looped triples.** A failing pure pool of fifteen cubes, all
   class counts at most three, cannot contain two own-looped triples.

For (1), see [Argument 12](#arg-12), the three four-copy proofs in
`../pure_supported/`, [Argument 29](#arg-29), and
[Argument 28](#arg-28). For (2), see
[Argument 38](#arg-38) and its explicit dependencies. For (3), see
Section4 of [Argument 33](#arg-33).

## 2. The deletion argument {.unnumbered}

Suppose a pure fifteen-cube failure exists. Every fourteen-cube subpool
is also a failure. Therefore every class has at most three copies:
any four copies could be retained in a fourteen-subpool, contradicting
the concentration bound.

At most eight classes are occupied, by the nine-distinct-class theorem.
Some class has size three. Otherwise fifteen cubes in at most eight
classes, each of size at most two, force seven doubled classes. Select
two copies from six of those classes and any two additional sources;
the resulting fourteen-pool has six repeated classes and solves.

Now take any triple class T and delete one of its cubes. The resulting
fourteen-pool still fails and has an occupied class of size two. It
cannot be a failure with no own-looped triple, since such a failure
has only triple and singleton classes. Thus it contains an own-looped
triple U≠T. The same U is own-looped in the original fifteen-pool,
by monotonicity.

Apply this argument again, now taking T=U. It produces a second
own-looped triple different from U. This contradicts fact (3).
Therefore every pure fifteen-pool assembles.




# Argument 40: Five copies in one class, with diffuse opposite sources {#arg-40}

**Theorem.** A fourteen-pool containing five copies from an adjacent
tricolour class and at least one opposite-repeat source is soluble,
provided no opposite variety occurs more than twice.

Together with the separate pure-adjacent five-class theorem, this removes
every adjacent class of size five from the remaining diffuse branch.

## 1. Notation and two elementary bounds {.unnumbered}

Colours are 0,1,2,3,4, and `ab` denotes the directed tricoloured corner
a→b. Write C(S) for the cut S→Sᶜ. Its pole pair is its two-element side.
Its three varieties are indexed by the repeated colour outside that pair.
Thus four copies of a class contain a same-repeat pair, supplying both
bicoloured corners of a target of that class. Opposite varieties are
bidirected K₂,₂ graphs on four colours.

Normalize the distinguished class to A=C(01). Its six corners form a
two-by-three array with rows 0,1 and columns 2,3,4. The adjacent classes
disjoint from A are precisely

    B=C(234), Z23=C(23), Z24=C(24), Z34=C(34).

The reverse of A has three two-corner columns q→{0,1}. A B source sees
all three, and a Z source sees two entire columns. Every opposite source
meets A, and also its reverse, in either two corners in different columns
or four corners forming a two-column rectangle. Moreover a two-corner
intersection determines the opposite variety uniquely: its two undirected
edges determine the omitted colour and the bipartition.

We also use the shared-four bound: two adjacent classes with four common
corners have at most seven copies in a failure. Otherwise choose a class
with at least four copies, reserve a same-repeat pair for its bicoloured
corners and two further copies for its two private tricoloured corners,
and fill the four common corners from the other four sources.

## 2. Three useful eight-cube constructions {.unnumbered}

Call an adjacent source **disjoint** if it has no tricoloured corner of A.

### Construction I: four A, three disjoint sources, one opposite source {.unnumbered}

Choose two reverse-A columns met by the opposite source. On these four
positions, every disjoint source sees one whole column or both. If the
three disjoint sources do not all see just the same single column, the
four sources have a perfect matching: the three disjoint sources jointly
see all four positions, and any two of them together with the opposite
source see at least three.

In the exceptional case all three disjoint sources have the same class:
each sees the common column and the third column. Retarget to those two
columns. The three sources are now universal on the four reverse
positions, and the opposite source still sees at least one. In either
case the four A copies fill the four forward positions of the resulting
opposite target.

Consequently, if a failing pool contains at least four A and one opposite
source, it contains at most two sources disjoint from A.

### Construction II: three A, three disjoint sources, two opposite sources {.unnumbered}

Apply Construction I's reverse-half argument using the first opposite
source. The second opposite source meets the selected forward half,
because it meets at least two of the three A columns. It and three A
copies fill that half.

Consequently, if a failure contains at least three A and two opposite
sources, at most two adjacent sources are disjoint from A.

### Construction III: three A, four disjoint sources, one opposite source {.unnumbered}

The four disjoint sources match the reverse positions of some two-column
rectangle. If three of them miss the same column, select the other two;
otherwise every missing-column class occurs at most twice, and any two
columns work. This is Hall's theorem for two position pairs: at most two
sources are confined to either pair. The opposite source and three A
copies fill the forward half.

Consequently, if a failure contains at least three A and one opposite
source, at most three adjacent sources are disjoint from A.

## 3. Five A and two distinct opposite varieties {.unnumbered}

First we record a stronger two-disjoint-source construction:

> Four A, two disjoint adjacent sources, and two distinct opposite
> varieties always assemble an opposite target.

Here is an elementary three-column matching argument. Write P,Q for the
reverse-A intersections of the opposite sources. Each meets at least two
columns, and |P∪Q|≥3. Write Z,W for the two disjoint sources' reverse-A
intersections; each contains at least two complete columns.

If Z,W have two whole columns in common, select them. Both are universal
on the selected rectangle. If P,Q can fill two different positions there,
we are done. Otherwise both restrict to the same singleton. Each also
meets the third column, and their union on that column has at least two
positions. Retarget to the third column and the singleton's column:
P,Q fill the third column, and Z,W fill the other column.

The remaining case has Z and W missing distinct columns x,y. On the
rectangle x,y, they fill one position in each column, while P,Q fill the
other positions provided P and Q can be assigned different columns.
If this fails, both P,Q miss the same one of x,y, say y. They therefore
both meet x and the third column z. Retarget to x,z. The source W is
universal, while P,Q and Z match three positions: each has at least two
positions there, and their union has at least three. This completes the
reverse half; four A fill the forward half.

Replacing one A in this construction by a third opposite source gives
another useful eight-cube core: three A, two disjoint sources, and three
opposite sources with maximum variety multiplicity two always solve.
Indeed choose two distinct opposite varieties for the reverse-half
construction; the remaining opposite meets the selected forward half
and completes it with three A.

Consequently a failure with at least four A and two distinct opposite
varieties has at most one disjoint adjacent source. A failure with at
least three A and at least three diffuse opposite sources also has at
most one disjoint adjacent source.

We can now show that nine pieces suffice for the five-copy assertion:
five A, two distinct opposite varieties, and two arbitrary additional
sources.

Reserve a same-repeat A pair for the bicoloured positions of an A target.
If either of the two additional sources meets A, it and the two opposite
sources match three A corners. Each opposite sees at least two corners,
and their union has at least three, since a two-corner pattern uniquely
determines an opposite variety. Hall therefore gives the three-corner
matching; the three remaining A fill the other corners.

Otherwise both additional sources are adjacent and disjoint from A.
The stronger construction just proved solves using four A, those two
sources and the two opposite varieties.

We may therefore assume that the fourteen-pool contains just one opposite
variety O, with multiplicity t=1 or2.

## 4. A two-corner Hall cover {.unnumbered}

Let z count adjacent sources disjoint from A. Construction I gives z≤2.
After a same-repeat A pair is reserved for its bicoloured corners, three
A remain. Therefore the nine outside sources cannot match three A
corners in a failure.

By König's theorem their incidence graph has a vertex cover of size at
most two. Two source vertices cannot cover it, because at least seven
outside sources meet A. A source vertex and a corner vertex cannot
cover it either. For t=2, one opposite copy remains uncovered and sees
at least two corners. For t=1, the exceptional source must be O; all
eight other outside sources are then either disjoint or in the unique
adjacent class meeting A in that single corner. Since z≤2, that class
would contain at least six copies.

Hence all outside intersections are contained in two A corners H. The
intersection O∩A is exactly H. It is a pair in different columns, so up
to symmetry there are only two forms: a row pair or a diagonal pair.

## 5. Row pair: H={13,14} {.unnumbered}

Here O has corners ±{13,14,23,24}. The allowed outside adjacent classes
and their counts are

| Class | Symbol | Count | Intersection with A |
|---|---|---:|---|
| C(234) | B | b | empty |
| C(124) | D | d | 13 |
| C(123) | E | e | 14 |
| C(12) | F | f | 13,14 |
| C(23) | Z23 | c | empty |
| C(24) | Z24 | g | empty |
| C(34) | Z34 | h | empty |

Their total is 9−t. Each count is at most five, and the shared-four bound
gives d+f≤7 and e+f≤7. Write z=b+c+g+h.

The reverse-A position pools are as follows:

| Position | Adjacent classes containing it | O contains it? |
|---|---|---|
| 20 | B,D,E,F,Z23,Z24 | no |
| 21 | B,Z23,Z24 | no |
| 30 | B,E,Z23,Z34 | no |
| 31 | B,Z23,Z34 | yes |
| 40 | B,D,Z24,Z34 | no |
| 41 | B,Z24,Z34 | yes |

Four A can supply the forward positions of any rectangle target with
parts {0,1} and two of {2,3,4}.

### 5.1. Two O copies {.unnumbered}

Use the two O at31,41 in the rectangle on columns3,4. Positions30 and40
have at least two adjacent neighbours in their union, since their union
has size7−f≥2. Thus failure forces one position pool to be empty. By
interchanging3 and4, suppose b=e=c=h=0. Only D,F,Z24 remain, totalling7.

If g>0, use the rectangle on columns2,4:

    four A forward; O at41; Z24 at21;
    another D or Z24 at40; another D,F or Z24 at20.

This is possible since d+g=7−f≥2. Therefore g=0 and d+f=7. Both d,f
are at least two, and one is at least four.

If d≥4, reserve a same-repeat D pair and fill a D target by

    D:40,43; F:10,20; A:13; O:23.

If f≥4, reserve a same-repeat F pair and fill an F target by

    F:10,20; A:13,14; D:23; O:24.

Both constructions are possible, a contradiction.

### 5.2. One O copy {.unnumbered}

There are eight outside adjacent sources. Consider the rectangle on
columns3,4. Hall's theorem on its reverse positions30,31,40,41 says
that it solves unless at least one of the following holds:

    b+e+c+h=0;  b+d+g+h=0;  z=0;  d+f=7;  e+f=7.

For completeness: the first two alternatives are empty singleton pools;
the pair31,41 has only z+1 neighbours; the triples30,31,41 and31,40,41
have respectively9−d−f and9−e−f neighbours. All other Hall inequalities
follow from f≤5, d+f≤7 and e+f≤7.

If b+e+c+h=0, only D,F,Z24 remain. Now d+f≤7 forces g≥1, and
d+g=8−f≥3, so the columns2,4 construction above works. The second
empty-pool alternative is symmetric.

If z=0, only D,E,F remain, with total8. The shared-four bounds force
d,e≥1, and at least one is at least two. Assume d≥2. Assemble the
opposite target with parts {0,3} and {2,4}:

    A:02,04; O:32; E:34; D:40,43;
    two further D,E,F sources:20,23.

Every source in the last pool fits20. A remaining D or F fits23: failure
of that assertion would mean d=2,f=0,e=6, contrary to the class bound.

Finally suppose d+f=7; the case e+f=7 is symmetric. There is one other
outside adjacent source. If it is B,Z23 orZ24, use it at21 in the
columns2,4 rectangle, with D at40, F at20 and O at41. If it is E, the
z=0 case just proved applies. If it is Z34, one of d,f is at least four,
and the corresponding same-repeat construction of Section5.1 works.

Thus the row-pair case is always soluble.

## 6. Diagonal pair: H={02,14} {.unnumbered}

Here O is the opposite target with parts {0,4} and {1,2}. The allowed
outside adjacent classes are

    B=C(234), D=C(123), E=C(034), Z23, Z24, Z34,

with counts b,d,e,c,g,h, respectively. Their total is9−t, and again
z=b+c+g+h≤2. Every count is at most five.

In O itself, A supplies02,14. The remaining positions split into the
private triples

    L={10,20,24}, supplied by D;
    R={01,41,42}, supplied by E.

The disjoint sources B,Z24 meet L at20 and R at41; Z23 meets L at20,24;
Z34 meets R at41,42. The permutation (0 1)(2 4) interchanges D and E,
Z23 and Z34, and preserves A and O.

### 6.1. Two O copies {.unnumbered}

If z≤1 then d+e≥6. Since neither exceeds five,
min(d,3)+min(e,3)≥4. Use two A at02,14, four D/E sources in their
private triples, and the two O at the remaining two positions.

If z=2, try the rectangle on columns2,4, using four A forward and
the two O at20,41. The two disjoint sources can fill21,40 unless both
are Z23 or both are Z34. By symmetry take both to be Z34. If e>0,
assemble the rectangle on columns3,4 with

    four A forward; Z34:30,40; E:31; O:41.

If e=0, then d>0, and instead use Z34 at31,40, D at30 and O at41.

### 6.2. One O copy {.unnumbered}

Now d+e≥6. If d,e≥2, then min(d,3)+min(e,3)≥5. Use two A at02,14,
five D/E in their private triples, and O at the remaining position.

Otherwise symmetry gives d=1,e=5,z=2. If a disjoint source is B,Z23
orZ24, use

    A:02,14; E:01,41,42; D:10; disjoint source:20; O:24.

If both disjoint sources are Z34, use the columns3,4 construction of
Section6.1 with Z34 at30,40, E at31 and O at41.

This closes the diagonal case and proves the theorem.

## 7. A thirteen-cube corollary of the constructions {.unnumbered}

Sections 5 and 6 use at most four A copies in every assembly. Therefore
they also prove the following more local statement, without an initial
five-copy A class:

> Take four A, t copies of a single opposite variety O (t=1 or2), and
> 9−t adjacent sources, every one of whose A intersections is contained
> in the two-corner set O∩A. Suppose adjacent class counts are at most
> five and the shared-four bound holds. Then these thirteen cubes solve.

Construction I still supplies the required bound z≤2 on sources
disjoint from A. This corollary is useful when a Hall cover has one
exceptional source, which can simply be discarded.

## 8. What remains {.unnumbered}

This theorem does not classify all diffuse fourteen-pools. It reduces a
putative mixed diffuse failure to adjacent class counts at most four.
The three constructions give additional necessary conditions: a class
of size four has disjoint-adjacent mass at most two; a class of size
three has disjoint mass at most two when there are at least two opposite
sources, and at most three when there is just one.

The separate computer verification of the diffuse eight-cube lemma, if
used, further limits the total number of opposite sources to1,2,3 or4.
That last restriction has not been proved by the hand arguments here.



# Argument 41: Four adjacent copies and four diffuse opposite sources {#arg-41}

**Theorem.** A fourteen-pool containing at least four copies of one adjacent
tricolour class and at least four opposite-repeat sources, with no opposite
variety occurring more than twice, is soluble.

Indeed a stronger local assertion suffices: after the four opposite
sources fail to match four corners of that adjacent class, any two
additional adjacent sources complete a solution, unless one already
completes the adjacent target directly.

Use the notation of [Argument 40](#arg-40): `ab` is a directed
corner, C(S)=S→Sᶜ, and an opposite target is the bidirected K₂,₂ between
two disjoint pairs. Normalize the four-copy class to A=C(01).

## 1. Reduction to seven tiny configurations {.unnumbered}

Reserve a same-repeat pair from the four A copies for an A target's
bicoloured positions. If the four opposite sources match four of its
six tricoloured corners, the remaining two A complete the target.

Every opposite source meets A in two corners from different columns,
or in a four-corner rectangle. A two-corner intersection determines its
opposite variety uniquely. Hall's theorem consequently shows that the
four opposite sources fail to match four A corners only if all four
intersections lie in a common three-corner set H. Indeed a deficient
triple of sources would have the same two-corner intersection, giving
three copies of one opposite variety, which is excluded.

The four sources have matching rank three on H. Thus any additional
source having an A corner outside H completes the adjacent target.
We may assume that every additional source meets A only in H. This also
shows that the pool has exactly four copies of A. At most three opposite
varieties have their A intersections in H, so at most six opposite
sources occur in total. There are therefore at least four other adjacent
sources; we may select any two as helpers.

In A's two-by-three corner array, H has one of three shapes:

1. Three corners of one row: normalize H={02,03,04}.
2. Two corners of one column and one of another: H={02,03,12}.
3. One corner in each column, split between the rows: H={02,03,14}.

The eligible opposite varieties correspond to pairs of H in different
columns. In the first and third shapes these are the three edges of a
triangle; in the second shape they form a two-edge path. Four sources
with each variety used at most twice give respectively two, one and
four possibilities up to symmetry. We handle these seven cases below.

## 2. Two matching observations {.unnumbered}

Suppose an opposite target T has exactly two A corners X. Put Y=T\X,
so |Y|=6, and let P′,Q′ be the intersections with Y of two helper sources.

* If there are two copies of T and two copies of another opposite U,
  with C=(U∩T)\X of size three, then the target solves whenever
  P′,Q′ are nonempty, |P′∪Q′|≥2 and P′∪Q′ is not contained in C.
  Two A fill X; the two U and the helpers match four Y positions;
  the two T fill the rest. Hall for these four sources has only two
  possible failures: the helpers jointly see one position, or all four
  sources jointly see only the three positions C.
* If there are two T and one each of U,V, and their residual
  intersections C_U,C_V partition Y into triples, the same assignment
  works whenever P′,Q′ are nonempty and |P′∪Q′|≥2. All other Hall
  inequalities follow from the two disjoint triples.

All helpers in the following tables are adjacent sources. The tables
are obtained simply by intersecting directed cuts with the named target
and deleting its two A corners.

## 3. Three corners in one row {.unnumbered}

Set

    R = opposite 02∣34, omitting1;
    S = opposite 03∣24, omitting1;
    T = opposite 04∣23, omitting1.

These are precisely the eligible opposite varieties. By symmetry the
four opposite sources are either 2S+2T or R+S+2T.

The helper classes and their residual intersections are:

| Helper | S minus its A corners02,04 | T minus its A corners02,03 |
|---|---|---|
| C(234) | 20,40 | 20,30 |
| C(02) | 23 | 24 |
| C(03) | 32,34 | 34 |
| C(04) | 43 | 42,43 |
| C(034) | 32 | 42 |
| C(024) | 23,43 | 43 |
| C(023) | 34 | 24,34 |
| C(23) | 20,34 | 20,24,30,34 |
| C(24) | 20,23,40,43 | 20,43 |
| C(34) | 32,40 | 30,42 |

### 3.1. Two S and two T {.unnumbered}

In either target S or T, the other opposite variety's residual triple
is {20,34,43}. The first matching observation and the table show:

* S can fail only when both helpers belong to
  {C(04),C(023),C(23)}, or they are two C(02), or two C(034).
* T can fail only when both helpers belong to
  {C(03),C(024),C(24)}, or they are two C(02), or two C(034).

The two displayed three-class families are disjoint. Only the two
doubled-helper cases remain. They both assemble R:

| Helpers | A | Helpers' positions | S positions | T positions |
|---|---|---|---|---|
| two C(02) | 03,04 | 23,24 | 32,40 | 30,42 |
| two C(034) | 03,04 | 32,42 | 23,40 | 24,30 |

### 3.2. One R, one S, two T {.unnumbered}

In T, the residual intersections of R and S are the disjoint triples
{24,30,42} and {20,34,43}. By the second matching observation the only
exceptions are two helpers from the same singleton row of the T column:
two C(02), C(03), C(034), or C(024).

The symmetry interchanging2 and3 exchanges the first two and the last
two cases. For two C(02), assemble R using A at03,04, the helpers at23,24,
R at40, S at32, and T at30,42. For two C(034), use A at03,04, the helpers
at32,42, R at40, S at23, and T at24,30.

This closes the row shape.

## 4. Two corners in a column {.unnumbered}

Here H={02,03,12}. The opposite sources are

    two T = opposite04∣23, omitting1;
    two U = opposite02∣13, omitting4.

The helper classes are C(234), C(134), C(04), C(034), C(024), C(23),
C(24), C(34).

If either helper is C(234), C(034), C(23) or C(34), it contains31.
Assemble the opposite target01∣23 using four A for02,03,12,13, that
helper for31, T for20, U for21, and another T or U for30.

Thus both helpers belong to {C(134),C(04),C(024),C(24)}.

If one is C(134), assemble the target02∣34. Use two A at03,04 and
that helper at40. The other helper has at least one corner in
{23,24,30,32,42}. The two T meet this five-set in {24,30,42}, and the
two U meet it in {23,30,32}. After assigning the other helper anywhere
in the five-set, the two triples, with common point30, match its four
remaining positions using two T and two U.

If neither helper is C(134), both belong to {C(04),C(024),C(24)}.
All three classes contain41,43. Assemble the target04∣13 by

    A:03,14; helpers:41,43; T:30,34; U:01,10.

This closes the column shape.

## 5. Three columns, split between the rows {.unnumbered}

Here H={02,03,14}. Put

    T = opposite04∣23, omitting1;
    U = opposite04∣13, omitting2;
    V = opposite04∣12, omitting3.

These are the eligible opposite varieties. The eligible helpers have
the following residual intersections:

| Helper | T minus02,03 | U minus03,14 | V minus02,14 |
|---|---|---|---|
| C(234) | 20,30 | 30,41 | 20,41 |
| C(04) | 42,43 | 01,41,43 | 01,41,42 |
| C(123) | 20,24,30,34 | 10,30,34 | 10,20,24 |
| C(034) | 42 | 01,41 | 01,41,42 |
| C(024) | 43 | 01,41,43 | 01,41 |
| C(23) | 20,24,30,34 | 30,34 | 20,24 |
| C(24) | 20,43 | 41,43 | 20,41 |
| C(34) | 30,42 | 30,41 | 41,42 |

Interchanging2 and3 exchanges U and V. There are four opposite-source
multisets up to this symmetry.

### 5.1. Two U and two V {.unnumbered}

For either target the other variety's residual triple is {01,10,41}.
By the first matching observation, the U construction can fail only
if both helpers are C(034), and the V construction can fail only if
both are C(024). They cannot both fail.

### 5.2. Two T and two V {.unnumbered}

The common residual triple is {20,24,42}. The T construction can fail
only for two C(034) or two C(024); the V construction can fail only
for two C(23). Again one construction works.

### 5.3. One T, one U, two V {.unnumbered}

In V, the residual intersections of T and U are the disjoint triples
{20,24,42} and {01,10,41}. Every helper sees at least two positions of
V outside A, so the second matching observation always applies.

### 5.4. Two T, one U, one V {.unnumbered}

In T, the residual intersections of U and V are the disjoint triples
{30,34,43} and {20,24,42}. The second observation works unless the
helpers are both C(034) or both C(024). By interchanging2 and3 it is
enough to treat two C(034). Assemble V using

    A:02,14; helpers:01,41; T:20,24; U:10; V:42.

This closes the last shape and proves the theorem.




# Argument 42: Four adjacent copies and three diffuse opposite sources {#arg-42}

**Theorem.** A fourteen-pool containing at least four copies of an
adjacent tricolour class and exactly three opposite sources, with no
opposite variety occurring three times, is soluble.

Use the directed-corner notation of [Argument 40](#arg-40).
The nine-piece lemma there handles any adjacent class of size at least
five, since the three opposite sources include two distinct varieties.
We may therefore suppose that every adjacent class has at most four
copies. Normalize the distinguished four-copy class to A=C(01).

We will use the following already proved eight-cube construction:

    3B + two adjacent sources disjoint from B + three diffuse O solve.

Thus any class of size at least three in a putative failure has at most
one adjacent source disjoint from it.

## 1. Reduction to three-corner covers {.unnumbered}

Reserve a same-repeat A pair for its bicoloured positions, leaving two
A. The three opposite sources have matching rank three on A: each sees
at least two corners, and three sources with only two corners between
them would be three copies of one opposite variety.

Suppose their union on A has at least four corners. A nonempty adjacent
source fails to extend them to a four-matching only if two of the
opposite sources are identical, have a two-corner A intersection P,
and the adjacent source's intersection is contained in P. This follows
directly from Hall: a deficient triple is the only possible obstruction,
since the four-source union already has size at least four.

There are seven other adjacent sources, and at most one is disjoint
from A. Consequently either an adjacent target solves at once, or all
seven adjacent sources have their A intersections in the same pair P.
The thirteen-cube corollary in the five-class note then solves using
four A, the two identical opposite sources and those seven adjacent
sources; the third opposite is unnecessary.

It remains that the three opposite sources' union on A is a set H of
size three. Any further source meeting A outside H extends their
three-matching and solves A. We may therefore assume all seven other
adjacent sources meet A only in H.

Up to the stabilizer of A there are three shapes for H, treated below.

## 2. A row triple: H={02,03,04} {.unnumbered}

The eligible opposite varieties are

    opposite02∣34, opposite03∣24, opposite04∣23,

all omitting colour1. Two distinct such varieties can match q0,r0 for
any two different columns q,r in {2,3,4}: their sets of available
columns are different two-element subsets of a three-element set.

Every eligible adjacent helper has at least one reverse-A position q1.
It has only one such position exactly when its class is C(0q); all
other eligible classes have at least two. Hence two helpers match q1,r1
for some distinct columns unless both are the same class C(0q).

The seven helpers cannot all belong to one class, since class counts
are at most four. Choose two with a matching to q1,r1, and choose two
distinct opposite sources at q0,r0. Four A fill0q,0r,1q,1r, completing
the rectangle target with parts {0,1} and {q,r}.

## 3. A column pair: H={02,03,12} {.unnumbered}

The opposite sources use both varieties

    T = opposite04∣23, omitting1;
    U = opposite02∣13, omitting4,

one twice and the other once. The three sources match20,21,30: use
T at20, U at21 and the repeated variety at30. Thus any helper at31
completes the rectangle01∣23 with four A.

The eligible helpers containing31 are C(234), C(034), C(23), C(34).
If none occurs, the remaining helper classes are

    D=C(134), R=C(04), S=C(024), Z=C(24).

If D occurs with any of R,S,Z, assemble the rectangle01∣24 using

    four A forward; T:20; U:21; D:40; R,S orZ:41.

Seven helpers cannot all be D, so D is absent in a failure. Likewise,
if Z occurs, some R or S occurs, and the same construction uses Z at40
and that other source at41. Thus Z is absent too.

The seven helpers are therefore R and S. One class has four copies,
and the other has three. If R has four, reserve a same-repeat R pair.
The remaining two R fill two of its six tricoloured positions; the
three opposite sources and one A match four more. Explicitly:

| Opposite counts | A | T copies | U copies |
|---|---|---|---|
| two T, one U | 02 | 42,43 | 01 |
| one T, two U | 02 | 42 | 01,03 |

If S has four, reserve a same-repeat S pair and use one R with the
three opposite sources for four tricoloured positions:

| Opposite counts | R | T copies | U copies |
|---|---|---|---|
| two T, one U | 01 | 03,43 | 21 |
| one T, two U | 01 | 43 | 21,23 |

The two remaining S fill the other two positions. This closes the
column-pair shape.

## 4. Three columns, split between the rows: H={02,03,14} {.unnumbered}

Write

    T = opposite04∣23, omitting1;
    U = opposite04∣13, omitting2;
    V = opposite04∣12, omitting3.

These are the eligible opposite varieties. Their reverse-A intersections
are respectively {20,30}, {30,41}, {20,41}. Thus any two distinct
opposite sources match any prescribed pair of positions from
P={20,30,41}.

Let K={21,31,40}. If two helpers match two K positions, select the
corresponding rectangle:21,31 uses columns2,3;21,40 uses2,4;31,40
uses3,4. Two distinct opposite sources fill its other two reverse
positions from P, and four A fill the forward half.

We may therefore suppose the helpers have matching rank at most one
on K. Their K intersections are:

| Helper class | K intersection |
|---|---|
| R=C(04) | empty |
| D=C(123) | empty |
| E=C(034) | 31 |
| F=C(024) | 21 |
| C(234), C(23), C(24), C(34) | at least two positions |

If one of the last four classes occurs, all six other helpers must be
R or D; any other nonempty K intersection would give a two-matching.
But R and D are reverse cuts and hence disjoint. Two counts totalling
six, each at most four, have one at least three and the other at least
two, contradicting the disjoint-source bound of the introduction.

Thus none of the last four classes occurs. Also E and F cannot both
occur. Interchanging2 and3 if necessary, assume F is absent. Write
r,d,e for the counts of R,D,E, with r+d+e=7.

Every eligible opposite source meets each of R and D in four corners.
Since A meets each of them, three opposite sources and one A match
four corners of either class. Four copies of R or D would therefore
solve after reserving a same-repeat pair. Hence r,d≤3.

Suppose e=4. Since D and E are disjoint, the disjoint-source bound gives
d≤1, so r≥2. In E the opposite intersections lie in

    M={01,02,41,42}:
    T sees02,42; U sees01,41; V sees all four.

The three opposite sources match three M positions, since no variety
occurs three times. An R source sees all M and fills the fourth. After
reserving a same-repeat E pair, the two other E fill31,32. Thus e=4
also solves, and e≤3.

The class D is disjoint from both R and E. If d=3, its disjoint mass
would be r+e=4. If d=2, then r+e=5 forces r or e to be three, and that
class has two disjoint D sources. Both violate the disjoint-source
bound. Therefore d≤1; since r+d+e=7 and r,e≤3, necessarily

    r=3, d=1, e=3.

This last form assembles V directly. Four of the six R/E sources fill
their common positions M. An A fills14. Of the three remaining target
positions {10,20,24}, two can be filled by opposite sources: T sees20,24,
U sees10, and V sees all three; failure to find a two-matching would
require three U copies. The D source fills the last position.

All three cover shapes are soluble. This proves the theorem.

## Consequence {.unnumbered}

Combining this theorem with [Argument 41](#arg-41)
shows, entirely elementarily, that a mixed fourteen-cube failure with
at least three opposite sources, each variety used at most twice, has
every adjacent class count at most three. The one- and two-opposite
four-class branches are treated in their respective companion notes.



# Argument 43: Four adjacent copies and two distinct opposite sources {#arg-43}

**Theorem.** A fourteen-pool containing four copies of an adjacent
tricolour class and exactly two opposite sources of different varieties
is soluble.

The earlier nine-piece construction excludes any adjacent class of
size at least five. Suppose therefore that all adjacent classes have
size at most four, and normalize the distinguished class to A=C(01).
The notation and elementary constructions are those of the other notes
in this directory.

## 1. The Hall-cover reduction {.unnumbered}

Four A contain a same-repeat pair for the bicoloured positions of an A
target. The other two A fill two arbitrary tricoloured positions, so
the ten outside sources must have matching rank at most three on A
in a failure.

The eight-cube construction 4A+two disjoint adjacent sources+two distinct
opposite sources shows that at most one outside adjacent source is
disjoint from A.

A vertex cover of the outside/A incidence graph therefore cannot have
at most one corner vertex. With no corner vertices it would leave at
least seven disjoint sources. With one corner vertex, both opposite
sources must be exceptional source vertices, leaving at least seven
adjacent copies in the unique class meeting A in that single corner.

If the cover consists of two corners and one source vertex, the
exceptional source must be opposite: two different opposite varieties
cannot both have their A intersections in a two-corner set. The other
opposite source and all eight adjacent sources are then contained in
that pair. The thirteen-cube corollary of the five-class note solves
using four A, that one opposite source and the eight adjacent sources.

It remains that all outside incidences lie in three A corners H. The
two different opposite sources occupy different two-corner subsets of
H, so their union is H. Again H has three possible shapes.

## 2. Row triple: H={02,03,04} {.unnumbered}

The opposite sources omit colour1. Their reverse-A row0 intersections
are different two-element subsets of {20,30,40}, and hence they match
q0,r0 for any two distinct columns q,r.

Every eligible adjacent helper has at least one position q1. It has
exactly one precisely for the three classes C(02),C(03),C(04). Two
helpers therefore match q1,r1 unless both are the same one of these
classes. The eight helpers cannot all be one class, since its count
would exceed four. Choose a suitable pair of helpers and assemble
the rectangle01|qr with four A forward and the opposite sources and
helpers on its reverse half.

## 3. Column pair: H={02,03,12} {.unnumbered}

The opposite sources are

    T=opposite04∣23, omitting1;
    U=opposite02∣13, omitting4.

They can fill any prescribed two of {20,21,30}. Thus the rectangle
01∣23 solves if two helpers can fill31 and a position in {20,21,30}.

The eligible helper classes, restricted to these four reverse positions,
are

| Helper | Available reverse positions |
|---|---|
| C(234) | 20,21,30,31 |
| C(134) | 30 |
| C(04) | empty |
| C(034) | 31 |
| C(024) | 21 |
| C(23) | 20,21,30,31 |
| C(24) | 20,21 |
| C(34) | 30,31 |

Suppose some helper contains31, but the required helper pair cannot be
chosen. Hall on the two categories {31} and {20,21,30} says either no
helper meets the second category, or only one helper meets their union.
The first alternative puts all eight helpers in C(04),C(034), which
share four corners and thus have combined count at most seven. The
second leaves at least seven copies of C(04), contradicting its class
bound. Hence in a failure no helper contains31.

The helpers are therefore among

    D=C(134), R=C(04), S=C(024), Z=C(24).

Now use the rectangle01∣24: T fills20 and U fills21. D sees40, R and S
see41, and Z sees both. If both positions40,41 occur among the helpers,
two different helpers can fill them, since every helper sees at least
one and there are eight helpers. Otherwise all helpers are D, violating
the class bound, or all are R,S, violating their shared-four bound seven.

This closes the column shape.

## 4. Split triple: H={02,03,14} {.unnumbered}

The eligible opposite varieties are

    T=opposite04∣23, omitting1;
    U=opposite04∣13, omitting2;
    V=opposite04∣12, omitting3.

Any two distinct varieties match any prescribed pair from
P={20,30,41}. As in the three-opposite proof, if two helpers match a
pair from K={21,31,40}, those two helper positions and the corresponding
two P positions form the reverse half of an A rectangle, which solves.

The K intersections are:

| Helper | K intersection |
|---|---|
| R=C(04) | empty |
| D=C(123) | empty |
| E=C(034) | 31 |
| F=C(024) | 21 |
| C(234),C(23),C(24),C(34) | at least two |

If a helper from the last four classes occurs and the helpers have
K-rank at most one, all seven other helpers must be R or D. Their
counts are three and four. They are reverse cuts, so four of one,
three of the other and one opposite source solve by the elementary
4A+three-disjoint+O construction.

Thus no helper from the last four classes occurs. Nor can E and F
both occur. Interchanging2 and3 if necessary, take F absent, and write
r,d,e for the counts of R,D,E. Then r+d+e=8. Since R,E share four
corners, r+e≤7 and therefore d≥1. Since d≤4, we also have r+e≥4.

Assemble V. Four R/E sources fill their common positions
{01,02,41,42}. One A fills14. Of the remaining positions {10,20,24},
the two opposite sources fill two different ones: T sees20,24, U sees10,
and V sees all three, so any two different varieties have a two-matching.
One D fills the last position.

This proves the theorem.

## Consequence {.unnumbered}

Together with the preceding notes, every mixed fourteen-pool with an
adjacent class of size at least four is soluble whenever at least two
different opposite varieties occur. The homogeneous two-opposite and
one-opposite cases are proved in their respective companion notes.



# Argument 44: Four adjacent copies and two identical opposite sources {#arg-44}

**Theorem.** A fourteen-pool containing four copies of an adjacent
tricolour class and exactly two opposite sources, both of the same
variety, is soluble.

We use the notation and proved constructions of the five-class note.
Its theorem already excludes adjacent class counts at least five, so
all such counts may be assumed at most four. Normalize the chosen
four-copy class to A=C(01), and write O for the opposite variety.

The following bounds hold in a failure:

* At most two adjacent sources are disjoint from A, by
  4A+three-disjoint+O.
* A class of size at least three has disjoint-adjacent mass at most
  two, by 3B+three-disjoint+two-O.
* Two adjacent classes sharing four corners have combined count≤7.

## 1. Hall reduction {.unnumbered}

Reserve a same-repeat A pair, leaving two A for tricoloured positions.
The ten outside sources must have matching rank at most three on A.
A vertex cover with no corner vertices would leave at least seven
disjoint sources. A cover with one corner and two source vertices must
use both source vertices for the opposite copies, leaving at least
six adjacent sources in one singleton-intersection class. Both are
impossible.

For a cover with two corners and one exceptional source, use the
thirteen-cube corollary in the five-class note: if an adjacent source
is exceptional, retain the two O and seven covered adjacent sources;
if an O is exceptional, retain the other O and all eight adjacent
sources. Therefore all remaining cases have a three-corner cover H.

In particular O∩A has size two. If O met A in four corners, neither
of the possible covers could contain even one of its copies, and
the pool would already solve. The two corners form either a row pair
or a diagonal pair in A's two-by-three array.

## 2. Row pair, with H itself a row: H={02,03,04} {.unnumbered}

Normalize O to opposite04∣23, omitting1, so O∩A={02,03}.
Its two copies fill20,30 in the reverse half of rectangle01∣23.
Thus helpers matching21,31 complete the rectangle with four A.

If no such helper pair exists, one of21,31 is absent: otherwise only
one helper could meet either position, leaving at least seven helpers
in C(04), the unique eligible class missing both. Interchanging2 and3,
suppose21 is absent. The eight helpers then belong to

    X=C(03), Y=C(04), Z=C(034), W=C(34).

If W occurs, use one W at40 in rectangle01∣34 and one O at30.
The seven remaining helpers match31,41: each sees at least one, and
neither position can be absent without forcing seven copies of X or Y.
Thus W is absent.

Let x,y,z be the remaining class counts, with x+y+z=8. Four X solve:
reserve a same-repeat pair, use two X at31,32, A at04, O at34, and
two Y/Z sources at01,02. Four Y solve using two remaining Y at01,41,
two A at02,03 and the two O at42,43. Thus x,y≤3.

If z=4, then x+y=4 and both x,y are positive. Reserve a same-repeat
Z pair; two Z fill01,32, while X fills31, Y fills41, O fills42 and
A fills02. Hence z≤3. The counts are therefore a permutation of3,3,2.

### Repeated-colour contradiction {.unnumbered}

Each class has a loop: two copies with the same repeated colour solve.
Here are the tricoloured assignments after reserving the indicated pair:

| Target and reserved pair | Six tricoloured positions |
|---|---|
| X, two X | Z:31,32; A:04; O:34; Y:01,02 |
| Y, two Y | Z:01,41; A:02,03; O:42,43 |
| Z, two Z | X:31,32; Y:41,42; A:02; one further X/Y:01 |

The last extra source exists because x+y≥5.

The three classes also conflict pairwise whenever they use the same
repeated colour:

* **X,Y:** reserve one of each for an X target's bicoloured corners.
  Use Z at31,32, A at04, O at34, and two remaining X/Y/Z at01,02.
* **X,Z:** their only possible common repeat is4. They supply an A
  target's poles0,1. Four A fill12,13,14,02; a remaining X fills04
  and a Y fills03.
* **Y,Z:** their only possible common repeat is3. They again supply
  an A target's poles0,1. Four A fill12,13,14,04; a remaining Y
  fills03 and an X fills02.

Consequently all eight X/Y/Z copies would have different repeated
colours, impossible with five colours. This closes the row cover.

## 3. Row pair, with H={02,03,12} {.unnumbered}

Again O is opposite04∣23. The helper classes are

    B=C(234), D=C(134), R=C(04), E=C(034), F=C(024),
    Z23=C(23), Z24=C(24), Z34=C(34).

Only D has an A corner outside O∩A. If d≤1, discard that source and
apply the thirteen-cube corollary with the other seven helpers. Thus
d≥2. Also R cannot occur four times: after reserving an R pair, use
the other two R at01,41, two A at02,03 and the two O at42,43. Hence r≤3.

Try rectangle01∣34, using O at30 and three helpers at31,40,41.
The helper pools are

    31: B,E,Z23,Z34;
    40: B,D,Z24,Z34;
    41: B,R,E,F,Z24,Z34.

All pair and triple Hall bounds hold: the first two pools have union
8−r−f≥2 since d≥2; the first and third have union8−d≥4; the last
two have union8−z23≥6. The40 pool is nonempty, and the41 pool has at
least8−d−z23≥2 sources. Thus failure forces31 to be absent.

Only D,R,F,Z24 remain. In rectangle01∣24, use O at20 and ask the
helpers to fill21,40,41. The pools are F+Z24, D+Z24 and R+F+Z24.
Their pair unions have sizes at least5,4 and8 respectively. The last
two pools are nonempty; the first is nonempty as well, since otherwise
d+r=8 contradicts d≤4,r≤3. Hall gives the required three-matching.

## 4. Row pair, with H={02,03,14} {.unnumbered}

Write

    R=C(04), D=C(123), E=C(034), F=C(024),

and let z count the other four, disjoint-from-A classes. Only D meets
A outside O∩A, so d≥2 by the thirteen-cube corollary. As above r≤3.

D is disjoint from R,E,F. If d≥3, the disjoint-mass bound gives
r+e+f≤2. Since d+r+e+f+z=8 and z≤2, this forces d=4,z=2.
But every disjoint-from-A source meets D in a corner of O. A meets
D at14, outside O. Therefore two O, one such source and one A match
four D corners; after reserving a D pair, the two remaining D complete
the target. Hence d=2 and r+e+f=6−z≥4.

If z>0 and a disjoint source sees40, use it there. Another helper
sees21 or31: either another disjoint source exists, or e+f>0, since
z=1,e=f=0 would give r=5. A further R/E/F source fills41. Together
with O at20 or30 these helpers complete rectangle01∣24 or01∣34.

If no disjoint source sees40, all z sources are C(23). They can fill
21,31 with each other or with E/F; again e+f>0 when z=1. The two O
fill20,30 and rectangle01∣23 solves. Thus z=0.

If E and F both occur, they fill31,21 with the two O at20,30, solving
the same rectangle. Otherwise interchange2 and3 so F is absent.
Now r+e=6. Assemble opposite04∣12: four R/E sources fill their common
positions01,02,41,42; A fills14; D fills10; the two O fill20,24.

Sections 2–4 prove the theorem whenever O has a row-pair intersection
with the chosen four-copy class. We may use this conclusion for any
other four-copy class as well.

## 5. Diagonal pair, with H={02,03,12} {.unnumbered}

Now O is opposite02∣13, omitting4. The helper classes are the same
as in Section 3. Every class among D=C(134), R=C(04), F=C(024) has
either four O corners or a row-pair O intersection. By Section 1 or
Sections 2–4, its count is at most three.

Also E=C(034) has count at most three. If it had four, reserve a
same-repeat pair. O fills01,32 and A fills02. Every other eligible
helper class has a corner in {31,41,42}; use one there and the two
remaining E at the other two positions. There is such a helper since
the total helper count is eight.

Let d,r,e,f≤3 be these counts and z≤2 the disjoint-from-A mass.
Try rectangle01∣34, with O at30 and helpers at31,40,41. As in Section 3,
their pair unions have sizes8−r−f≥2,8−d≥5,8−z23≥6. The41 pool
cannot be empty. Thus failure forces either31 or40 to be absent.

* If31 is absent, the only helpers are D,R,F,Z24. If Z24 occurs,
  rectangle01∣24 solves with O at21 and helpers at20,40,41: use
  Z24 at20, and the remaining helpers match40,41. Indeed d+z24≥2,
  since d=0,z24=1 would force r+f=7>6. If Z24 is absent, then
  d+r+f=8, so each count is at least two. Assemble O itself using
  A:03,12; D:10,32; F:21,23; R:01; O:30.
* If40 is absent, the only helpers are R,E,F,Z23. If Z23 occurs,
  rectangle01∣23 solves with the two O at21,30 and helpers at20,31:
  Z23 supplies20, and another Z23 or E supplies31. Such another
  source exists, since e=0,z23=1 would force r+f=7>6. If Z23 is
  absent, then r+e+f=8, with each count at least two. Assemble O
  using A:03,12; O:10,30; F:21,23; E:32; another helper:01.

This closes the first diagonal shape.

## 6. Diagonal pair, with H={02,03,14} {.unnumbered}

Now O is opposite04∣12, omitting3. Let

    R=C(04), D=C(123), E=C(034), F=C(024).

Each has either four O corners or a row-pair intersection, so all
four counts are at most three by the established cases.

Try O itself. Two A fill02,14. For its six other positions

    Y={01,10,20,24,41,42},

the helper intersections are

| Helper | Intersection with Y |
|---|---|
| R,E | 01,41,42 |
| D | 10,20,24 |
| F | 01,41 |
| C(234),C(24) | 20,41 |
| C(23) | 20,24 |
| C(34) | 41,42 |

If the helpers match four Y positions, the two O fill the rest.
Suppose their rank is at most three. Every helper has at least two
Y positions. A cover with two Y vertices and one source vertex would
put at least seven helpers into one identical two-position pattern;
the table and the bounds f≤3,z≤2 make that impossible. Therefore all
helper intersections lie in three Y positions.

Unless those positions are {01,41,42}, the table permits at most five
helpers: at most three from D or F and at most two disjoint-from-A
sources. Consequently all helpers belong to R,E,F,Z34=C(34).

Write z for the Z34 count. We have r+e+f+z=8, with r,e,f≤3,z≤2.
If f>0, assemble opposite12∣34, omitting0. Use A at13,14, F at23,
O at24, and fill31,32,41,42 from R,E,Z34. This four-matching exists:
E and Z34 see all four positions, R sees41,42, and

    e+z≥8−r−f≥2,     r+e+z≥5.

If f=0, necessarily r=e=3,z=2. Assemble rectangle01∣34 using four A
forward, O at41, E at31, and the two Z34 at30,40.

All cases are soluble, proving the theorem.

## Consequence and remaining gap {.unnumbered}

All mixed four-class branches with at least two opposite sources are
elementary-closed, whether the opposite varieties are distinct or
identical. The companion one-opposite proof extends the conclusion to
every mixed diffuse fourteen-cube failure: all adjacent class counts
are at most three.



# Argument 45: One opposite source: the row-triple Hall cover {#arg-45}

We use directed corners `ab`, adjacent cuts C(S)=S→Sᶜ, and opposite
varieties given by bidirected complete bipartite graphs on two pairs.
Suppose a putative fourteen-cube failure contains four A=C(01), one
O=opposite04|23, and nine adjacent helpers. Suppose every helper meets
A only in H={02,03,04}. Adjacent class counts are at most four, and
classes sharing four tricoloured corners have combined count at most
seven. Both bounds have already been proved for a failure.

Write Q={2,3,4}. The eligible helper classes are

    Fi=C(0i),  Gi=C({0}∪(Q\{i})),  Zi=C(Q\{i})  (i∈Q),
    B=C(Q).

The Zi and B are precisely the helpers disjoint from A. We will show
that this covered configuration always solves.

## 1. A disjoint helper gives an opposite assembly {.unnumbered}

For any helper X, let L(X) be the set of columns q for which X has
the reverse-A corner q1. Then

    L(Fi)={i};  L(Gi)=L(Zi)=Q\{i};  L(B)=Q.

Choose a disjoint helper Z. It has q0 and q1 for every q in a set
M of at least two columns. O has the reverse-A positions20,30, so
write P={2,3} for its columns. Let U be the union of the L sets of
the other eight helpers.

We have |U|≥2. For any two columns in U, two of these eight helpers
can fill their two q1 positions: otherwise at most one helper meets
either column, leaving at least seven helpers in the unique singleton
class Fi of the third column, contrary to the class bound four.

If distinct columns q∈M∩U and r∈P∩U can be chosen, assemble the
rectangle01|qr: Z supplies q0, O supplies r0, two other helpers supply
q1,r1, and four A supply the forward half.

The only way those distinct columns cannot be chosen is M=P={2,3}
and U={2,4} or {3,4}. Indeed all three of M,P,U have size at least
two in a three-element set; if both intersections are the same
singleton, M and P have the same missing column.

Thus Z=C(23), and by interchanging2 and3 we may take U={3,4}. The
other helpers are then F3,F4,G2 or C(34). If C(34) occurs, choose it
as Z instead: its column pair differs from P, and the preceding
rectangle construction works. Therefore the sole disjoint helper is
C(23), and the other eight helpers are F3,F4,G2.

Let their counts be x,y,z. Since F3,G2 and F4,G2 share four corners,
x+z≤7 and y+z≤7. Their total is eight, so x,y≥1. Assemble the
opposite target14|23, omitting0, by

    A:12,13;  C(23):21;  O:24,

and fill31,34,42,43 from F3,F4,G2. These helpers see respectively
{31,34}, {42,43}, {31,42}. Assign F3 to34 and F4 to43. The remaining
helpers match31,42: each position still has at least three neighbours,
because x+z=8−y≥4 and y+z=8−x≥4.

Consequently a failure in this row cover has no disjoint helpers.

## 2. The six-position path {.unnumbered}

Write a,b,c,d,e,f for the counts of F2,F3,F4,G2,G3,G4, respectively.
Their sum is nine, and each is at most four.

Consider the opposite target14|23. Two A supply12,13. Its remaining
six positions, in the order

    24,21,43,42,31,34,

have the following helper neighbourhoods:

* F2,G3,F4,G2,F3 are the five consecutive edges of this six-vertex path;
* G4 sees the outer four positions24,21,31,34;
* O sees the two ends and the two central positions24,43,42,34.

The four pairs of consecutive path-edge classes share four corners.
Thus their weight sums a+e, e+c, c+d, d+b are at most seven.

We now check Hall's theorem for these six positions.

* A set of five or six positions meets every helper, so is safe.
* A set of four positions can miss at most one path-edge class; it
  cannot miss G4. Hence it has at least9−4=5 helper neighbours.
* The complement of a three-position set contains at most two path
  edges. If it contains two, they are consecutive and have combined
  weight at most seven. G4 cannot be missed, and O must meet the
  chosen three positions. There are therefore at least9−7+1=3
  neighbours.

Only singleton and pair obstructions remain. The singleton positions
not already supplied by O are21 and31. Their failure conditions are

    a+e+f=0,              b+d+f=0.

For a pair, if O misses it then the pair is {21,31}, which has
9−c≥5 helper neighbours. Otherwise a deficient pair must have no
helper neighbour at all. For the central pair {43,42}, this means
c+d+e=0. For any other pair, G4 meets it, so f=0. Nine remaining
copies, each path-edge class of weight at most four, require at least
three positive path edges in the four-position complement. Those
three edges must form four consecutive vertices. The resulting
conditions are the two singleton conditions already listed, or
a+b+f=0.

Therefore failure of this opposite target forces one of

    a+e+f=0;   b+d+f=0;   c+d+e=0;   a+b+f=0.

The first three put all helpers in one of the families

    {F3,F4,G2},  {F2,F4,G3},  {F2,F3,G4}.

The fourth puts them in {F4,G2,G3}. This last family actually solves
another opposite target. Its counts c+d+e=9 obey c+d≤7,c+e≤7, so
d,e≥2. Assemble opposite12|34 by

    A:13,14;  O:24;  G3:23;  G2:31,32.

Two of the six remaining helpers fill41,42: every one sees41, and
at least c+d−2≥3 also see42.

Thus only the first three support families need to be considered.

## 3. The three support families {.unnumbered}

Interchanging2 and3 exchanges the first two families and preserves O.
It suffices to treat these two forms:

| Case | X | Y | Z |
|---|---|---|---|
| I | F3=C(03) | F4=C(04) | G2=C(034) |
| II | F2=C(02) | F3=C(03) | G4=C(023) |

Write x+y+z=9, with each count at most four.

Four copies of X or Y solve by reserving a same-repeat pair and using
the following six tricoloured positions. The two positions in the last
column are supplied by two sources from the other two classes; at least
five such sources are available.

| Case and target | Two remaining target-class copies | A | O | Two sources from the other classes |
|---|---|---|---|---|
| I, X | 31,32 | 04 | 34 | 01,02 |
| I, Y | 41,43 | 03 | 42 | 01,02 |
| II, X | 21,23 | 03 | 24 | 01,04 |
| II, Y | 31,32 | 02 | 34 | 01,04 |

Hence x,y≤3. If z=4, then x+y=5 and x,y≥2. Reserve a same-repeat Z
pair. In Case I use X at31,32, Y at41,42, A at02 and a remaining Z
at01. In Case II use X at21,24, Y at31,34, A at04 and a remaining
Z at01. Thus z=4 also solves. Necessarily x=y=z=3.

### Each class has a loop {.unnumbered}

The same Z-target construction works after reserving two of its three
copies. For X and Y, the following assignments work after reserving
their same-repeat pair:

| Case and target | Remaining target copy | Z | A | O | Two copies of the other class |
|---|---|---|---|---|---|
| I, X | 31 | 32 | 04 | 34 | Y:01,02 |
| I, Y | 43 | 41 | 03 | 42 | X:01,02 |
| II, X | 23 | 21 | 03 | 24 | Y:01,04 |
| II, Y | 32 | 31 | 02 | 34 | X:01,04 |

Thus all three copies of each class must have different repeated colours.

### The three classes conflict pairwise {.unnumbered}

If X and Y share a repeated colour, reserve one of each for an X
target's bicoloured positions. There are now two X copies left, so
the X row of the preceding four-copy table supplies the six tricoloured
positions. Two sources from Y,Z remain available for its common pair.

If X and Z share a repeated colour, they supply the bicoloured corners
of an A target: X has pole0, Z has pole1, and their common repeat lies
outside {0,1}. The same holds for Y and Z. In either case, one remaining
X and one remaining Y match two different A corners, and four A fill
the other four. Their A intersections are different two-element
subsets of {02,03,04}, so this two-matching always exists.

The three repeated-colour sets must therefore be pairwise disjoint.
Each has size three, requiring nine colours where only five exist.
This contradiction closes the row-triple cover.



# Argument 46: Four adjacent copies and one opposite source {#arg-46}

**Theorem.** Every fourteen-pool containing exactly one opposite-repeat
source and at least four copies from one adjacent tricolour class is
soluble.

Use directed corners `ab`, adjacent classes C(S)=S→Sᶜ, and opposite
varieties given by bidirected complete bipartite graphs on two pairs.
The mixed five-class theorem already handles a class of size at least
five. In a putative failure, therefore, every adjacent class has count
at most four. Normalize a four-copy class to A=C(01).

We use the established shared-four bound and two eight-cube constructions:

    4B + three adjacent sources disjoint from B + O solve;
    3B + four adjacent sources disjoint from B + O solve.

Thus a four-copy class has disjoint-adjacent mass at most two, and a
three-copy class has disjoint-adjacent mass at most three.

## 1. A two-corner transfer lemma {.unnumbered}

Suppose the nine adjacent sources outside A meet A only in a two-corner
set P. Then four A together with those helpers and O solve.

If O∩A⊆P, retain any eight helpers and use the thirteen-cube corollary
of [Argument 40](#arg-40).

Otherwise O has an A corner outside P. Apply the explicit two-corner
cover constructions in Sections 3–5 of
[Argument 12](#arg-12). Their numerical assumptions
hold here: our class bound four is stronger than the bound five there,
the shared-four bound is unchanged, and the disjoint mass is at most
two. All of those constructions use at most four A except the
two conflicts between A and a singleton-intersection class in the
final row-cover case. In either such conflict one A has been reserved
for a bicoloured position, and four A were used at the four corners
outside P. Here use O at one of those corners and the three remaining
A at the other three. Every other displayed construction transfers
without change. This proves the lemma.

This use of the pure five-class proof concerns its displayed post-cover
constructions. The initial five-A matching-rank reduction is not needed.

## 2. Hall reduction and the rectangle exclusion {.unnumbered}

Reserve a same-repeat A pair for its bicoloured positions, leaving two
A. The ten outside sources must have matching rank at most three on
A's six tricoloured positions. König's theorem gives a cover with at
most three source/corner vertices.

A cover without a corner vertex leaves at least seven adjacent sources
disjoint from A, impossible. A cover with one corner vertex must use
an exceptional source vertex for O. Even if another adjacent source is
exceptional, at least eight adjacent sources remain covered by that
single corner. At most two are disjoint, so at least six belong to
the unique singleton-intersection class, again impossible.

For a cover with two corners and one exceptional source, use Section 1
if O is exceptional. If an adjacent source is exceptional, the other
eight helpers and O lie in the pair O∩A, and the thirteen-cube corollary
applies directly.

Consequently every remaining case has a three-corner cover H for all
outside sources. O∩A has exactly two corners, in different columns.
In particular, **a four-copy class meeting O in four corners already
solves**. We may use this rectangle exclusion for any other class.

Up to the stabilizer of A, there are five covered configurations:
three with O∩A a row pair, and two with O∩A a diagonal pair.

## 3. Row pair, with H={02,03,04} {.unnumbered}

Normalize O to opposite04|23, omitting1. This is precisely the case
proved in [Argument 45](#arg-45).

That proof first solves whenever a helper is disjoint from A. With
no disjoint helpers it reduces one opposite target to a six-position
path matching problem. Hall sets of size at least three are controlled
by the shared-four bound. The remaining singleton and pair conditions
reduce to three support families, each of which forces three looped,
pairwise conflicting classes with counts3,3,3. The resulting demand
for nine different repeated colours is impossible.

## 4. Row pair, with H={02,03,12} {.unnumbered}

Again O is opposite04|23. The nine eligible helpers belong to

    B=C(234), D=C(134), R=C(04), E=C(034), F=C(024),
    Z23=C(23), Z24=C(24), Z34=C(34).

Only D meets A outside O∩A. If d≤1, discard that source and apply
the thirteen-cube corollary to eight helpers contained in O∩A.
Hence d≥2. Also r≤3 by the rectangle exclusion: R has four O corners.

Try rectangle01|34, with O at30 and helpers at31,40,41. Their pools are

    31: B,E,Z23,Z34;
    40: B,D,Z24,Z34;
    41: B,R,E,F,Z24,Z34.

The pair unions have sizes9−r−f≥2,9−d≥5,9−z23≥7. The40 pool is
nonempty since d≥2, and the41 pool has at least9−d−z23≥3 sources.
Thus Hall can fail only when31 is absent.

Only D,R,F,Z24 then remain. Use rectangle01|24, with O at20 and
helpers at21,40,41. These pools are F+Z24, D+Z24 and R+F+Z24.
Their pair unions have sizes at least6,5 and9. The last two pools are
nonempty. The first is also nonempty, since otherwise d+r=9 would
contradict d≤4,r≤3. The required three-matching exists.

## 5. Row pair, with H={02,03,14} {.unnumbered}

O is still opposite04|23. The nonzero-intersection helper classes are

    R=C(04), D=C(123), E=C(034), F=C(024).

Write z≤2 for the other helpers, which are disjoint from A. Only D
meets A outside O∩A, so d≥2 as above. Both R and D have four O
corners, so r,d≤3 by the rectangle exclusion.

D is disjoint from R,E,F. If d=3, its disjoint mass would be
r+e+f=9−d−z≥4, contrary to the three-copy disjoint-mass bound.
Therefore d=2, and r+e+f+z=7.

One D and O fill20,30 in rectangle01|23. If two other helpers match
21,31, the rectangle solves with four A. At least e+f+z=7−r≥4
helpers meet one of21,31. Hence absence of such a two-matching forces
one position to be absent. Interchanging2 and3, assume21 is absent.
Then F,B,Z23,Z24 are absent, and the disjoint helpers are all Z34.
Thus r+e+z=7.

If z>0, use Z34 at40 and O at30 in rectangle01|34. Two remaining
R/E/Z34 helpers match31,41: after reserving that Z34, the31 pool
has e+z−1≥3 sources, and all six remaining helpers see31 or41.

Thus z=0. The bounds r≤3,e≤4 and r+e=7 force r=3,e=4. Reserve a
same-repeat E pair. The two other E fill31,32. R sees all four common
corners01,02,41,42, and O sees02,42, so the three R and O fill those
four positions. This assembles E.

Sections 3–5 prove that a four-copy class with a row-pair O intersection
solves. We may now use that conclusion for any helper class as well.

## 6. Diagonal pair, with H={02,03,12} {.unnumbered}

Now O is opposite02|13, omitting4. The eligible helper classes are
the same as in Section 4. D=C(134) and F=C(024) each have four O
corners; R=C(04) has a row-pair O intersection. Their counts d,r,f
are therefore at most three.

E=C(034) also has count at most three. If e=4, reserve a same-repeat
E pair, put O at32 and A at02, and let two other helpers fill two
different positions in {01,31,41,42}; the two remaining E fill the
other two. Such a helper pair exists. Each of the five other helpers
meets this set. Those with only one position are D at42, Z23 at31,
and Z24 at41; each such class has count at most three (indeed the
disjoint classes have total at most two). Every other eligible helper
sees at least two positions. Five helpers therefore cannot all be
confined to one common position.

Now d,r,e,f≤3 and z≤2. Try rectangle01|34 with O at30 and helpers
at31,40,41. Its pair unions have sizes9−r−f≥3,9−d≥6,9−z23≥7,
and the41 pool is nonempty. Failure forces31 or40 to be absent.

If31 is absent, only D,R,F,Z24 remain. When Z24 occurs, rectangle01|24
solves with O at21, Z24 at20 and two helpers at40,41. After reserving
the Z24, the40 pool has d+z24−1≥2 sources and the41 pool has at
least five. When Z24 is absent, d+r+f=9 forces d=r=f=3. Assemble O
using A:03,12; D:10,32; F:21,23; R:01; O:30.

If40 is absent, only R,E,F,Z23 remain. If Z23 occurs, both E and F
occur, because otherwise the total helper count is at most3+3+2=8.
Use rectangle01|23 with O:30, Z23:20, E:31, F:21 and four A forward.
Thus only r=e=f=3, with no disjoint helpers, remains.

### The remaining repeated-colour triangle {.unnumbered}

The three classes R,E,F all have loops. After reserving a same-repeat
pair from the named target class, use:

| Target | Six tricoloured positions |
|---|---|
| R | A:02,03; E:41,42; F:01,43 |
| E | remaining E:31; O:32; A:02; R:41,42; F:01 |
| F | remaining F:21; O:23; A:03; R:41,43; E:01 |

They also conflict pairwise. R and E can share only repeat3, and R and
F only repeat2. In either case their poles supply0,1 for an A target.
Four A fill04,12,13,14; a remaining E fills02 and a remaining F fills03.

If E and F share a repeat, reserve one of each for an E target's poles
1,2. The two remaining E fill31,32, A fills02, two R fill41,42, and
O fills01. Thus E and F also conflict.

Three pairwise disjoint repeated-colour sets of size three would be
required, a contradiction.

## 7. Diagonal pair, with H={02,03,14} {.unnumbered}

Here O is opposite04|12, omitting3. Let

    R=C(04), D=C(123), E=C(034), F=C(024).

R,D,E each have four O corners, and F has a row-pair O intersection.
Consequently r,d,e,f≤3. The disjoint-from-A count is z≤2, and
r+d+e+f+z=9.

Try O itself. Two A fill02,14, and the other six positions split into

    C={01,41,42},       L={10,20,24}.

R and E see all C; F sees01,41. There are at least four R/E/F sources,
and r+e≥1, since otherwise the total count is at most3+3+2=8.
Therefore three R/E/F sources match all C.

D sees all L. The disjoint helpers have L intersections

    B=C(234), Z24: {20};   Z23: {20,24};   Z34: empty.

If two sources from D and the disjoint classes match two L positions,
O fills the third and the target solves. Otherwise d≤1; and if d=1,
all disjoint sources must be Z34.

Write z34 for the Z34 count. We now try opposite12|34, omitting0:

    A:13,14;  F:23;  O:24;

then fill31,32,41,42 from R,E,Z34. E and Z34 see all four positions,
while R sees41,42. This works whenever

    f>0,        e+z34≥2,        r+e+z34≥4.

The last inequality always holds under the remaining assumptions.
If d=1, all disjoint sources are Z34, giving r+e+z34=8−f≥5.
If d=0, it is at least9−f−z≥4.

If f=0, the count bounds force d=1,r=e=3,z=2, with both disjoint
sources Z34. Assemble rectangle01|34 using four A forward, O at41,
E at31, and the two Z34 at30,40.

Finally suppose e+z34<2. This cannot happen when d=1, since then
e+z34=8−r−f≥2. When d=0, we have e≥1, and the bounds force
e=1,z34=0,r=f=3,z=2. The two disjoint sources cannot match two L
positions, so both are B or Z24; a Z23 together with either would
give a two-matching. Both B and Z24 contain21,40,41. Assemble
rectangle01|24 with four A forward, O at20, the two disjoint sources
at21,40, and one R at41.

All cases are soluble. This proves the theorem.

## Cumulative consequence {.unnumbered}

Together with the preceding mixed four-class proofs, this establishes:

> A mixed diffuse fourteen-cube failure has every adjacent
> tricoloured-corner class count at most three.

The result is elementary and independent of the finite eight-cube
lemma for high opposite-source counts. It does not close the remaining
mixed cases in which all adjacent class counts are at most three.



# Argument 47: Two own-loop triples with one opposite source {#arg-47}

**Theorem.** A failing pool of fourteen adjacent sources and one opposite
source, with adjacent-class multiplicities at most three, has at most one
triple admitting an own completion. The opposite source may participate
in either asserted completion.

We adapt [Argument 33](#arg-33), retaining
its notation and its explicit final matchings. Only the following changes
are needed; none assumes a completion avoiding the opposite source.

## 1. The two anchors {.unnumbered}

The repeat-restoration argument in Section 1 of that proof still applies:
restore an anchor copy when removing the other reserved source from an
own completion. It follows that two own-completed triples have disjoint
pole pairs. Normalize them to
\[
A=C(01),\qquad B=C(23)\quad\hbox{or}\quad C=C(014).
\]
The eight other adjacent sources have poles $04,14,24,34$, with forced
repeats $1,0,3,2$, respectively. Denote the opposite source by $O$.

For the disjoint orientation $A,B$, use target $01\mid23$. An adjacent
helper meets one of its directed halves. The source $O$ meets both:
its intersection with $A$ meets at least two of the three columns, hence
meets the rectangle on columns $2,3$; its corners are invariant under
reversal. Put the helper in one half and $O$ in the other, and fill the
remaining three positions in each half with the two anchor triples.

## 2. The nested orientation {.unnumbered}

For $A,C$, retain the names $P,\bar P,Q,\bar Q,R,\bar R,S,\bar S$
and the main/outer blocks from Section 3 of the pure proof. Put
\[
a=g(\bar P)+g(\bar Q),\qquad b=g(R)+g(S).
\]
Its three restrictions remain valid:

1. $a,b\le3$. Here use Construction III of
   [Argument 40](#arg-40): three copies of an adjacent class,
   four sources disjoint from it and one opposite source assemble.
   The first outer block is disjoint from $C$, and the second from $A$.
2. A main class of size three excludes every outer source. The displayed
   repeated-colour constructions in the pure proof use only the anchors,
   that main class and the outer source; they are unchanged.
3. If both main blocks occur, every main count is at most one. Again the
   displayed constructions use only adjacent sources and remain unchanged.

There is an outer source: otherwise eight adjacent helpers would lie in
the main classes. One occupied main block has capacity at most six, while
two occupied blocks have total capacity at most four by restriction 3.
Consequently every main count is at most two. With one main block the
main total is at most four, and with two the same bound follows from
restriction 3. Hence $a+b\ge4$ and both outer blocks occur.

The reverse-square argument from Section 3 of the pure proof now applies
without alteration. If three outer types occur, their at least four
copies fill the reverse square of $01\mid23$, while three $A$ and one
$C$ fill its forward square. Thus the outer classes can be normalized to
\[
\bar P^a,R^b,\qquad 1\le a,b\le3,\qquad a+b\ge4.
\]
There are exactly eight adjacent helpers, so the main total is $8-a-b$.
These are precisely the hypotheses of the pure proof's “remaining
numerical cases.” Its assignments to $04\mid23$ and $13\mid24$ use only
adjacent sources and therefore apply verbatim. Each case assembles,
contradicting failure.

The two alterations from the pure proof are the use of Construction III
to bound the outer blocks, and the capacity argument establishing an
outer source. In particular, neither argument requires the asserted own
completions to avoid $O$.



# Argument 48: Five repeated adjacent classes and two further classes {#arg-48}

## Theorem {.unnumbered}

Take adjacent-repeat sources from seven different tricoloured-corner
classes, with multiplicities

    3,2,2,2,2,1,1.

These thirteen sources contain an eight-source five-colour assembly.
In particular a pure fourteen-cube failure cannot have exactly one
triple class.

The proof classifies five fixed doubled classes by a small geometric
Hall table, then gives explicit helper constructions. It does not
enumerate source inventories or repeated-colour refinements.

Throughout C(S) means the directed cut S→Sᶜ. A label such as01
denotes its outset, and a target written ab/cd has all eight directed
corners between the pairs ab andcd. Its two four-corner halves are
ab→cd andcd→ab. All sources may be properly rotated independently.

## 1. The Hall criterion for five doubled classes {.unnumbered}

Take two sources from each of five distinct adjacent classes, and
fix an opposite target T that their union supports. These ten sources
match T if and only if no three target corners are private to one
of the five classes.

Necessity is immediate: two source copies cannot fill three corners
available only in their class. For sufficiency, an adjacent cut meets
T in either two positions or one of its full four-position halves.
At most two classes can have their whole intersection in two given
positions. Therefore sets of six positions see at least three of
the five classes, hence six sources. Sets of seven or eight positions
see all five classes. Supported singletons and pairs have at least
two source neighbours. A three- or four-set can fail Hall only if
all its corners have neighbours in just one class, giving a private
triple.

Suppose a five-set S fails Hall. It then meets at most two classes.
Those two class intersections must cover all five positions because
T is supported. Two two-position intersections cannot do so. If both
intersections have size four, they must be opposite target halves:
equal halves would cover only four positions. They are disjoint, so
one class supplies at least three private positions of S. If one
intersection has size four and the other size two, at least three
positions of S are outside the latter intersection and are private
to the former. Thus every Hall failure again gives a private triple.
This proves the criterion.

## 2. Classifying the five doubled classes {.unnumbered}

If their tricoloured union supports no opposite target, the elementary
support-poset theorem puts them inside a common-corner family or a
butterfly family. See Section0 of
[Argument 15](#arg-15); the theorem
there concerns arbitrary cut collections, not just a fixed source
count. Five distinct classes in a butterfly are, up to its symmetries,
one of the two sets

    F1={01,02,124,123,12},
    F2={01,02,124,12,012}.                            (F)

These omit a low class or a high class from the six-class butterfly.
Its four high classes are interchanged by the permutations1↔2,
3↔4, and(1 3)(2 4) followed by reversal of all cuts. The last
operation also exchanges its two low classes. This verifies the
two possible omissions directly.
The common-corner alternative will be handled directly in Section3.

Now suppose a target is supported but none assembles. By Section1
some class has three private target positions. An adjacent cut meeting
an opposite target in at least three positions contains an entire
four-position directed half, since its only possible intersection
sizes and shapes are two positions or a full half. Its private triple
therefore consists of three positions in that half. Normalize this
class to A=C(01) and those positions to

    03,04,13.

The other four classes must avoid those three corners. The implications
0∈S⇒3,4∈S and1∈S⇒3∈S give exactly these eight possible outsets:

    U={234,134,123,034},     V={13,23,24,34}.

If three of the four classes belong to U, or three belong to V,
two copies each of those three classes and A already assemble.
The direct constructions are Section2 of
[Argument 28](#arg-28); they use only those eight
sources. Thus exactly two classes lie in each of U,V.

The following table treats all six choices from U against all six
choices from V. An ordinary entry is an opposite target supported
by the five classes and having no three positions private to one
class. Section1 therefore gives an assembly. Each entry is checked
by intersecting the five directed cuts with its eight positions.
The exceptional entries I,II,III are identified immediately below.

| U pair / V pair | 13,23 | 13,24 | 13,34 | 23,24 | 23,34 | 24,34 |
| --- | --- | --- | --- | --- | --- | --- |
| 234,134 | 01/24 | 13/24 | 01/24 | 12/34 | I | I |
| 234,123 | 01/24 | 13/24 | 01/24 | I | I | 12/34 |
| 234,034 | 01/24 | 13/24 | 01/24 | 12/34 | I | I |
| 134,123 | III | 02/34 | III | 12/34 | 01/24 | 12/34 |
| 134,034 | 01/24 | 03/14 | II | 12/34 | 01/24 | 01/24 |
| 123,034 | 01/23 | 12/34 | 04/12 | 12/34 | 01/24 | 12/34 |

The three exceptional representatives are

    I   ={01,234,02,014,012},
    II  ={01,02,124,024,24},
    III ={01,02,124,023,012}.                         (E)

Here are explicit relabellings for all nine exceptional cells,
so their identification requires no orbit enumeration. The tuple
lists the new labels of0,1,2,3,4. A final reversal reverses every
directed cut simultaneously.

| U pair | V pair | Representative | Relabelling tuple | Reverse cuts? |
| --- | --- | --- | --- | --- |
| 234,134 | 23,34 | I | (0,1,2,3,4) | yes |
| 234,134 | 24,34 | I | (0,1,2,4,3) | yes |
| 234,123 | 23,24 | I | (0,1,3,4,2) | yes |
| 234,123 | 23,34 | I | (0,1,4,3,2) | yes |
| 234,034 | 23,34 | I | (1,0,2,3,4) | yes |
| 234,034 | 24,34 | I | (1,0,2,4,3) | yes |
| 134,123 | 13,23 | III | (0,3,1,4,2) | yes |
| 134,123 | 13,34 | III | (0,3,2,4,1) | yes |
| 134,034 | 13,34 | II | (1,0,3,2,4) | no |

This proves the required classification: unless the ten doubled
sources already assemble, the five classes either have one common
corner, form one of(F), or form one of(E).

## 3. The common-corner case {.unnumbered}

One of the five repeated classes has a third actual source. The
five classes therefore have counts3,2,2,2,2 through a common corner.
They contain a3,2,2,2,1 subpool, which assembles by
[Argument 23](#arg-23).

The two singleton helpers are unnecessary in this case. This is
the only point of the proof that uses the third source in a
repeated class.

## 4. The butterfly case F1 {.unnumbered}

The four high classes01,02,124,123 are all doubled. Their union
with the two low classes12,012 misses precisely31,32,41,42.
Any class outside the six-class butterfly contains at least one
of these four corners. At most one of the two distinct helper
classes is the remaining low class012, so an outside helper exists.

If it has31, target03/14 is assembled by

    helper:31; C01:04,13; C02:01;
    C124:40,43; C123:10,34.

Interchanging1,2 and interchanging3,4 preserve the doubled high
classes and act transitively on31,32,41,42. Thus any outside helper
works. This is also the explicit butterfly construction in the
six-doubled-classes note.

## 5. The butterfly case F2 {.unnumbered}

Write A=C01,P=C02,L=C124,Q=C12,H=C012, all doubled.

If a helper has41, use target01/24:

    helper:41; A:02,12; P:04,21; Q:20,14; L:40.

If a helper has42, use target02/14:

    helper:42; A:04,12; P:01,21; Q:10,24; L:40.

Otherwise both helpers avoid41,42. Outside the five core classes,
the only allowed helper classes are

    C03,C123,C13,C023,C23,C013.

Every one contains34; all except C123 contain31 or32. Since the
helpers have distinct classes, one can supply31 or32 and the other
can supply34. If the first supplies32, use target03/24:

    helpers:32,34; A:02,04; Q:20,23; L:40,43.

If it supplies31, use target03/14:

    helpers:31,34; P:01,04; Q:10,13; L:40,43.

This closes F2 using only two copies of every core class.

## 6. Exceptional type I {.unnumbered}

Write A=C01,B=C234,P=C02,D=C014,H=C012, all doubled.

A helper at32 gives target12/34:

    helper:32; A:13,14; B:31,41; P:23,24; D:42.

A helper at any corner c in {20,40,41} gives target01/24:

    helper:c; B:the other two corners of{20,40,41};
    P:04,21; D:02,12; H:14.

The only helper class outside the core avoiding both32 and all of
20,40,41 is C023. Two distinct helper classes cannot both be this
class, so one of the displayed constructions applies.

## 7. Exceptional type II {.unnumbered}

Write A=C01,P=C02,L=C124,R=C024,Z=C24, all doubled.

A helper at any corner c in {02,12,14} gives target01/24:

    helper:c; A:the other two corners of{02,12,14};
    P:04,21; L:20,40; R:41.

If neither helper meets that set, their only possible classes
outside the core are

    C234,C023,C23,C34.

Every one contains31, and all except C023 contain30. Distinct
helpers can therefore fill30,31 in target01/34. Its other six
positions are supplied by

    A:04,14; P:03; L:13,40; R:41.

This closes type II.

## 8. Exceptional type III {.unnumbered}

Write A=C01,P=C02,L=C124,R=C023,H=C012, all doubled.

A helper at any corner c in {10,40,43} gives target03/14:

    helper:c; L:the other two corners of{10,40,43};
    R:31,34; P:01,04; A:13.

If neither helper meets that set, their only possible classes
outside the core are

    C03,C034,C23,C013.

All except C23 contain32, so one of two distinct helpers contains
32. Use target03/12:

    helper:32; A:02,13; P:01,23; L:10,20; R:31.

Thus type III also assembles. All cases of the core classification
are now closed, proving the theorem.

## 9. Consequence for a pure fourteen-pool with one triple {.unnumbered}

In a hypothetical pure fourteen-failure, at most eight classes are
occupied and at most five have multiplicity at least two. Every
class has multiplicity at most three. If precisely one is a triple,
let d be the number of doubled classes and s the number of singletons.
Then

    3+2d+s=14,   1+d+s≤8,   1+d≤5.

These inequalities force d=4,s=3. Retain the triple, the four
doubled classes and two of the three singleton classes. The
thirteen-source theorem above gives an assembly, a contradiction.

Therefore every pure fourteen-failure has at least two triple
classes. This deduction uses the existing pure concentration,
diversity and six-repeated-class bounds; none depends on the
one-opposite fifteen-cube theorem.




# Argument 49: A private adjacent column and a high opposite source {#arg-49}

## Theorem {.unnumbered}

Let A=C(01), and take three sources of class A and eleven other
adjacent sources, each tricoloured-corner class having multiplicity
at most three. Suppose none of the eleven outsiders contains either
corner 02 or 12. Adjoin the opposite source

    O=01|34={03,04,13,14},

where each undirected edge supplies both corner directions. These
fifteen sources contain an eight-source five-colour assembly.

No assumptions about own loops, private corners of other classes,
or the number of occupied classes are required. In particular, this
settles the high-intersection type of an opposite cube avoiding a
private column of an adjacent triple.

## 1. The eleven possible outsider classes {.unnumbered}

The forbidden corners 02,12 say that an outset S must satisfy
0∈S⇒2∈S and 1∈S⇒2∈S. Its size is two or three. The possible
classes besides A are exactly:

| Name | Class | Reverse-A corners |
| --- | --- | --- |
| P | C(02) | 21 |
| Q | C(12) | 20 |
| L3 | C(123) | 20,30 |
| L4 | C(124) | 20,40 |
| R3 | C(023) | 21,31 |
| R4 | C(024) | 21,41 |
| H | C(012) | none |
| B | C(234) | 20,21,30,31,40,41 |
| Z23 | C(23) | 20,21,30,31 |
| Z24 | C(24) | 20,21,40,41 |
| Z34 | C(34) | 30,31,40,41 |

Lower-case letters denote source counts. Their sum is eleven and
each count is at most three.

We use the elementary cut-containment facts already proved in
[Argument 1](#arg-1), Section 1:
on an opposite target every adjacent cut meets two or four directed
positions; at most three classes are confined to three specified
positions, and at most two to two specified positions.

## 2. Three high targets give a short count reduction {.unnumbered}

First use target 01|23. The three A sources cover its four forward
positions, while O covers both directions of 03 and 13. This target
assembles if and only if the outsiders satisfy all three conditions:

    corner 20 is supported;
    corner 21 is supported;
    at least one of 30,31 is supported.                 (1)

Necessity follows from the single corners 20,21 and the pair 30,31,
the latter having only O as a core neighbour. For sufficiency, check
Hall. A set of reverse positions containing both 20,21 has at least
five outsider neighbours: the only classes avoiding both are H and
Z34, with combined capacity six. A reverse triple containing just
one of 20,21 has at least two outsider neighbours: the avoiders of
{20,30,31} are P,R4,H, and those of {21,30,31} are Q,L4,H.
Either list accommodates at most nine sources. All four reverse
positions have at least eight outsider neighbours, because only H
avoids them. The smaller reverse sets are handled by (1) and the
one O source.

A set meeting the forward half and meeting O has four core
neighbours, so sets of size at most four are automatic. If it avoids
O it lies in {02,12,20,21}; its only potentially deficient case is
the full four-set, which has outsider neighbours at 20,21. For sets
of five or more positions, the cut-containment bounds and eleven
outsiders give more than the required neighbours: a five-set has
at least two outsider neighbours, a six-set at least five, and
seven- and eight-sets see all eleven. This proves (1).

By exchanging 3 and 4, target 01|24 assembles under the corresponding
conditions with the last line of (1) replaced by support of 40 or41.

Suppose neither target assembles. If both 20 and 21 were supported,
no outsider could have any of 30,31,40,41. The table would leave
only P,Q,H, with capacity nine, fewer than eleven. Hence 20 or21
is unsupported. Exchange 0 and1 if necessary to assume 21 is absent.
The table then leaves only

    Q, L3, L4, H, Z34,

so

    q+l3+l4+h+z34=11.                                  (2)

Now use target T=01|34, which is O itself. On its reverse half R,
O is universal and the three A sources have no neighbours. On
its forward half the four core sources A,A,A,O are universal.
The same Hall bounds show that T assembles precisely when the
outsiders have matching rank at least three on R.

On R the remaining outsider patterns are

    Q,H: empty;  L3:{30};  L4:{40};  Z34:R.

Equation (2), together with q,h≤3, gives l3+l4+z34≥5. If z34≥3,
three universal Z34 sources give rank three. If z34=2, some L3 or
L4 is present and also gives rank three. If z34=1, then l3+l4≥4;
both are positive since each is at most three, again giving rank
three. Therefore failure forces z34=0, and (2) becomes

    q+l3+l4+h=11.

Each of these four counts is two or three, and exactly one is two.
This is the entire residual: it was derived from three target tests,
without enumerating inventories.

## 3. Explicit own loops close the residual {.unnumbered}

The class H has an own loop whenever it is a triple: after reserving
two H sources, its six corners have this matching:

    A:03,04;  L3:14,24;  L4:13,23.

All required classes have at least two copies. A triple L3 also has
an own loop in the pool containing O. Reserve two L3 sources and use

    remaining L3:34;  O:30;  A:14;  L4:20;  Q:10,24.

Similarly a triple L4 has the loop

    remaining L4:43;  O:40;  A:13;  L3:20;  Q:10,23.

If h=3, at least one of L3,L4 is a triple, and its pole pair meets
H's pole pair 34. If h=2, both L3 and L4 are triples, and their pole
pairs 04 and03 meet. Thus there are two own-loop triples with
intersecting pole pairs in every residual case.

For completeness, such a pair always assembles. An own-loop triple
in a failure must use all three possible repeated colours, since
otherwise a same-repeat pair supplies its two bicoloured target
corners and its loop finishes. The two triples' three-element repeat
sets therefore intersect. Choose a common repeated colour, reserve
one source from each class for the first class's two bicoloured
corners, using the pole shared by the two classes for the source
from the second class. Start with the first class's own-loop
matching after two of its sources were removed. Restore one of
those universal sources, and remove the chosen source from the
second class; if it was used in the matching, the restored universal
source replaces it. This completes the first adjacent target.

The contradiction proves the theorem. This final argument is valid
even when the opposite source participates in the loop matching.




# Argument 50: A private adjacent column and a diagonal opposite source {#arg-50}

## Theorem {.unnumbered}

Take three sources of class A=C(01) and eleven other adjacent sources,
each class occurring at most three times. Suppose every outsider avoids
02 and12. Adjoin

    O={01,04,13,34}=03|14.

Every undirected edge denotes both directed corners. These fifteen
sources contain an eight-source five-colour assembly.

This is the diagonal-intersection type of an opposite source avoiding
a private column of A. Exchanging colours3,4 gives the other labelled
variety of the same type. No assumptions about other private columns,
own loops, or occupied-class counts are used.

## 1. Outsiders and two high-target tests {.unnumbered}

Use the eleven names from [Argument 49](#arg-49):

    P=C02, Q=C12, L3=C123, L4=C124,
    R3=C023, R4=C024, H=C012,
    B=C234, Z23=C23, Z24=C24, Z34=C34.

Their reverse-A intersections are displayed in that note. Write
x=z23, y=z24, w=z34 and use lower-case letters for all other counts.
Every count is at most three and their sum is eleven. Put

    L=b+l3+l4+q+x+y,       R=b+p+r3+r4+x+y,
    a=b+l3+x+w,            d=b+r4+y+w.

These are respectively the outsider neighbour counts of20,21,30,41.

Target01|23 assembles exactly when

    L≥1, R≥1, a≥1, L+w≥2.                           (I)

Target01|24 assembles exactly when

    L≥1, R≥1, d≥1, R+w≥2.                           (II)

Here is a direct Hall verification of(I). The core A,A,A,O supplies
the four forward positions through A and the two positions13,31
through O. The potentially deficient reverse sets are the singleton
corners20,21,30 and the pair{20,30}; their outsider neighbour counts
are precisely the four expressions in(I).

Every other reverse set is automatic under(I). The pair{20,21}
has at least five outsider neighbours, since only H,Z34 avoid it.
The pair{21,30} has at least two, since its only avoiding classes are
Q,L4,H. Pairs containing31 also have O and an outsider from their
other corner. A reverse triple containing both20,21 inherits five
outsider neighbours. The triple{20,30,31} inherits L+w≥2 neighbours;
the triple{21,30,31} has at least two by the same Q,L4,H bound.
The full reverse half sees all outsiders except H, hence at least
eight.

A set meeting A and O has four core neighbours. If it meets A but
avoids O, a four-position set must contain at least one of20,21,30,
which is supported by(I). For larger sets, use the elementary cut
bounds: at most three classes fit inside three specified target
positions and at most two fit inside two. Thus a five-set has at
least two outsider neighbours, a six-set at least five, and a seven-
or eight-set all eleven. These counts cover every remaining Hall
inequality. Necessity of(I) follows from its listed singleton and
pair sets. The argument for(II) follows by the symmetry
(0 1)(3 4), which preserves O and exchanges L,R and a,d.

## 2. If 20 or21 is absent {.unnumbered}

The same symmetry lets us assume R=0. All outsiders then belong to

    Q,L3,L4,H,Z34,

and

    q+l3+l4+h+w=11.                                (2)

Suppose w>0. Use target01|34 and put O at31. Its other three reverse
positions are30,40,41. If w≥3, three Z34 sources fill them. If w=2,
equation(2) and q,h≤3 give l3+l4≥3; choose one L3 or L4 at its
corner30 or40 and let the two Z34 sources fill the other positions.
If w=1, then l3+l4≥4, so both are positive; use L3:30,L4:40,Z34:41.

There is a remaining forward helper from Q or H: their combined
count is at least two because l3+l4+w≤9. It and three A sources
fill the forward half. Thus w>0 always gives an assembly.

Failure therefore forces w=0. The four counts q,l3,l4,h sum to eleven,
so they are 3,3,3,2 in some order. Section4 closes this family.

## 3. If both 20 and21 are present {.unnumbered}

Assume L,R≥1. If w>0, both(I) and(II) hold, so suppose w=0.
To fail both targets we need

    (a=0 or L=1) and (d=0 or R=1).                  (3)

The alternatives involving L=1 or R=1 are incompatible with eleven
outsiders. If L=R=1, the total is

    h+L+R-(b+x+y)≤5.

If L=1 and d=0, then b=r4=y=0 and the total is

    h+L+p+r3≤3+1+3+3=10.

The remaining mixed alternative is symmetric. Thus(3) forces a=d=0.
Consequently b=l3=x=r4=y=w=0, and only

    P,Q,L4,R3,H

remain, with

    p+q+l4+r3+h=11.                                (4)

Use O itself as a target, with positions

    01,10,04,40,13,31,34,43.

The two L4-only outer positions are40,43; the two R3-only outer
positions are31,34. If l4,r3≥1 and l4+r3≥3, these four positions
can be filled by L4,R3,O, using O to assist whichever class has
only one source, if necessary.

When p,q>0, finish with P:01,Q:10 and A:04,13. If p=0, equation(4)
forces q,l4,r3,h each to be at least two. Use

    L4:40,43; R3:01,34; O:31; Q:10; A:04,13.

If q=0, the symmetric explicit matching is

    R3:31,34; L4:10,43; O:40; P:01; A:04,13.

The possibility p=q=0 is excluded by total capacity. Hence this
target solves whenever l4,r3≥1 and l4+r3≥3.

Only three count forms remain:

1. l4=0 and p,q,r3,h are 3,3,3,2;
2. r3=0 and p,q,l4,h are 3,3,3,2;
3. l4=r3=1 and p=q=h=3.

These are direct consequences of(4), not an inventory list used as
a premise. All are closed in Section4.

## 4. Explicit loops finish all count forms {.unnumbered}

Two own-loop triples whose pole pairs intersect always assemble:
otherwise each triple must use all three allowed repeated colours;
choose a common repeat and use one cube from each at the bicoloured
corners of the first target. Restoring one universal cube in the
first class's loop matching replaces the reserved cube of the second
class if it was used. This argument is detailed in the high-type
note and remains valid when O is used in a loop.

### The family q,l3,l4,h=3,3,3,2 {.unnumbered}

A triple H has the loop

    A:03,04; L3:14,24; L4:13,23.

A triple L3 has the loop

    remaining L3:30; O:34; A:14; L4:20; Q:10,24.

A triple L4 has the loop

    remaining L4:43; O:40; A:13; L3:20; Q:10,23.

If h=3, one of L3,L4 is a triple and its poles meet H's poles34.
If h=2, both L3,L4 are triples and their poles04,03 meet. Thus the
family solves in every case.

### The families involving P,Q,L4,R3,H {.unnumbered}

Whenever p=3 and q≥2, P has the loop

    remaining P:21; O:01; A:03,04; Q:23,24.

Whenever q=3 and p≥2, Q has the loop

    remaining Q:20; O:10; A:13,14; P:23,24.

If p=q=3, these two triples have intersecting poles02,12 and solve
immediately. This includes the third count form above.

In the first count form, if p and q are not both three, then
r3=h=3 and p,q≥2. The H loop is

    A:03,04; P:23,24; Q:13,14,

and the R3 loop is

    remaining R3:34; O:31; A:04; P:01,21; Q:24.

Their pole pairs34 and14 intersect. In the second count form the
same reasoning gives l4=h=3 and p,q≥2. Use the same H loop and

    remaining L4:43; O:40; A:13; Q:10,20; P:23.

The pole pairs34 and03 intersect. Every matching uses distinct
physical sources and respects the minimum counts in its case.

This completes the theorem.




# Argument 51: A private adjacent column and a row opposite source {#arg-51}

## Theorem {.unnumbered}

Take three sources of class A=C(01) and eleven other adjacent sources,
each class having multiplicity at most three. Suppose every outsider
avoids02 and12. Adjoin the opposite source

    O={13,14,23,24}=12|34.

The resulting fifteen sources contain an opposite-target assembly.
Exchanging0,1 gives the other labelled row-intersection type.

Together with the high and diagonal notes, this proves the following
uniform statement: three sources of an adjacent class, eleven capped
adjacent outsiders avoiding one of its columns, and any opposite
source avoiding that column always assemble a five-colour target.

## 1. Notation and the two high-target tests {.unnumbered}

Use the eleven outsider classes of [Argument 49](#arg-49):

    P=C02, Q=C12, L3=C123, L4=C124,
    R3=C023, R4=C024, H=C012,
    B=C234, Z23=C23, Z24=C24, Z34=C34.

Put x=z23,y=z24,w=z34 and

    L=b+l3+l4+q+x+y,       R=b+p+r3+r4+x+y,
    a=b+l3+x+w,            c=b+l4+y+w.

These count the outsider neighbours of20,21,30,40 respectively.
All outsider counts are at most three, and sum to eleven.

The target01|23 assembles exactly when

    L≥1, R≥1, a≥1, L+w≥2.                           (I)

This is the Hall test proved in Section1 of
[Argument 50](#arg-50): on this target the present O
has exactly the same intersection {13,31} as the opposite source
in that note. The proof therefore transfers unchanged.

Exchanging3,4 preserves the present O, and gives the second test:
target01|24 assembles exactly when

    L≥1, R≥1, c≥1, L+w≥2.                           (II)

We will also use the following explicit completion on target

    T={12,14,23,34}.

If r3≥1,r4≥2 and p+r3+r4≥4, fill

    A:12,14; O:32; R3:34; R4:41,43;
    another source from P,R3,R4:21;
    one Q or H source:23.                            (C)

The unused source at21 exists by the total p+r3+r4≥4, since only
three of those sources have been used. Each of those three classes
has corner21. A Q or H supplies23 independently. If instead r4≥1,
r3≥2, interchange3,4 throughout(C); its last position becomes24,
also supplied by Q or H. All sources in either matching are distinct.

## 2. No outsider sees21 {.unnumbered}

Suppose R=0. Only Q,L3,L4,H,Z34 remain, so

    q+l3+l4+h+w=11.                                (2)

If w>0, use target01|34, put O at31, and fill the other reverse
positions30,40,41. For w≥3 use three Z34 sources. For w=2, the
inequality l3+l4+w≥5 gives an L3 or L4 source at30 or40; the two
Z34 sources fill the other positions. For w=1, it gives l3+l4≥4,
so both classes occur; use L3:30,L4:40,Z34:41. There is an unused
forward helper from Q or H because q+h≥2. It and three A sources
fill the forward half.

It remains that w=0. Then q,l3,l4,h sum to eleven, so each is at
least two. The target {02,04,23,34} has the explicit assembly

    A:02,04; Q:20,23; L3:34; L4:40,43; O:32.

Thus R=0 always solves.

## 3. No outsider sees20 {.unnumbered}

Suppose L=0. Only P,R3,R4,H,Z34 remain, and

    p+r3+r4+h+w=11.                                (3)

If w≥2, again use target01|34. With w≥3, put O at31 and use
three Z34 sources at30,40,41. If w=2, there is an R3 or R4 source
because r3+r4+w≥5. Use that source at31 or41, O at the other of
those two positions, and two Z34 sources at30,40. In either case
p+h≥2 supplies a forward helper from P or H, which completes the
forward half together with three A sources.

If w≤1, equation(3) implies

    p+r3+r4+h≥10.

All four counts are positive; otherwise the other three have total
capacity nine. Moreover r3+r4≥4 and p+r3+r4≥7. Thus one of r3,r4
is at least two, and completion(C), or its image under3↔4, works
using an H source at23 or24. This closes L=0.

## 4. Both20 and21 are supported {.unnumbered}

Now L,R≥1. If w>0, both high-target tests hold. Assume w=0.

### L=1 {.unnumbered}

The equation

    b+l3+l4+q+x+y=1

says that exactly one outsider occurs among those six classes.
The other ten outsiders are in P,R3,R4,H. Thus

    p+r3+r4+h=10.

Each of these four counts is positive, r3+r4≥4, and
p+r3+r4≥7. Completion(C), or its3↔4 image, works with an H
source. The exceptional outsider is not needed.

### L≥2 {.unnumbered}

If both high targets fail, (I) and(II) force a=c=0. Hence

    b=l3=l4=x=y=w=0.

The only outsiders are P,Q,R3,R4,H, with

    p+q+r3+r4+h=11,     q=L≥2.                     (4)

If p≥2, at least one of R3,R4 occurs: otherwise p+q+h≤9.
An R4 source gives target {01,02,14,24} by

    Q:10,20; A:02,14; P:01,24; R4:41; O:42.

An R3 source gives the3↔4 image of this matching. Thus p≥2 solves.

If p≤1, equation(4) gives

    r3+r4≥4,     p+r3+r4≥5.

Both R3,R4 are positive, since each count is at most three, and
at least one is at least two. Use completion(C), or its3↔4 image,
with one of the Q sources at23 or24. This solves the last case.

All possible values of L,R,w have been covered, proving the theorem.

## Uniform private-column consequence {.unnumbered}

An opposite source avoiding02 and12 has exactly five possible
varieties. It either omits colour2, giving the three pairings of
0,1,3,4, or omits0 or1, giving one pairing in each case. Their
three stabilizer types are:

| Type | Representative | Proof |
| --- | --- | --- |
| High rectangle | {03,04,13,14} | [Argument 49](#arg-49) |
| Diagonal pair | {01,04,13,34} | [Argument 50](#arg-50) |
| Row pair | {13,14,23,24} | This note |

If all of0,1,2 occurred in an opposite four-cycle avoiding both
edges02,12, its two-element bipartition part containing2 would
also need to contain0,1, impossible. This proves the five-variety
list directly.




# Argument 52: One opposite cube and fourteen adjacent cubes {#arg-52}

## Theorem {.unnumbered}

Any pool consisting of one opposite-repeat five-colour cube and
fourteen adjacent-repeat five-colour cubes contains eight cubes
assembling a five-colour 2×2×2 cube with monochromatic faces.

There is no multiplicity assumption in the statement. The necessary
class bounds arise from the already proved pure fourteen-cube theory.
The proof does not assume the fourteen-failure catalogue or the
general N5=15 theorem.

## 1. Elementary facts about a pure fourteen-failure {.unnumbered}

The previous structural work proves that every failing pool of
fourteen adjacent cubes has the following properties:

1. Every adjacent tricoloured-corner class has count at most three.
2. At most eight classes occur, and at most five classes occur twice
   or more.
3. At most one triple class has an own-orientation loop: a matching
   of its six tricoloured corners after two of its cubes are reserved.
4. Every triple without such a loop has exactly two private corners,
   forming one column of its two-by-three corner array. Its other
   four corners have an outsider matching.
5. If no triple has an own loop, the pool has butterfly support.

The dependency references are [Argument 39](#arg-39),
[Argument 33](#arg-33),
[Argument 36](#arg-36),
[Argument 37](#arg-37),
[Argument 32](#arg-32), and
[Argument 38](#arg-38).

The thirteen-source theorem
[Argument 48](#arg-48) now adds:

6. A pure fourteen-failure has at least two triple classes.

Indeed a pure failure has at least one triple by the previous
concentration and diversity results. If it has exactly one, properties
1 and2 force its counts to be3,2,2,2,2,1,1,1. The new theorem solves
the subpool retaining two of its singleton classes.

## 2. Add the opposite cube {.unnumbered}

Let P be the fourteen adjacent cubes and O the opposite cube.
Suppose P+O fails. Then P is itself a pure fourteen-failure.

If P has no own-loop triple, property5 places it in the butterfly
family. The earlier elementary lemma
[Argument 34](#arg-34) says that
any opposite cube added to such a failure gives an assembly.
This case is therefore impossible.

Otherwise P has precisely one own-loop triple U. By property6 there
is another triple A, which has no own loop. Property4 gives A a
private column and an outsider matching of its other four corners.

If O contains one of A's two private corners, reserve two A cubes,
put O at that private corner, use the remaining A at the other one,
and use the four outsider matches at the other four corners. Thus
A gains an own loop in P+O. The loop on U persists. The elementary
mixed two-own-loop theorem
[Argument 47](#arg-47)
excludes two such triples in a failing fifteen-pool with one
opposite source. Hence this case also assembles.

It remains that O avoids A's whole private column. Normalize A to
C(01) and the column to02,12. The eleven adjacent outsiders all
avoid those two corners by privacy. They have class cap three by
property1. An opposite variety avoiding02,12 has one of exactly
five forms, falling into three geometric types:

| Type | Representative edge set | Elementary proof |
| --- | --- | --- |
| High | {03,04,13,14} | [Argument 49](#arg-49) |
| Diagonal | {01,04,13,34} | [Argument 50](#arg-50) |
| Row | {13,14,23,24} | [Argument 51](#arg-51) |

Those three notes prove that three A sources, the eleven capped
adjacent outsiders and O always assemble. Their proofs use small
Hall tests and explicit source allocations; the high and diagonal
types finish with intersecting own-loop triples.

This excludes the last possibility. Therefore every pool of one
opposite and fourteen adjacent cubes assembles, as claimed.




# Argument 53: Eleven adjacent cubes through one directed corner {#arg-53}

**Theorem.** Eleven adjacent-repeat cubes whose tricoloured-corner
classes all contain one fixed directed corner assemble a five-colour
target, provided every class has multiplicity at most three.

No opposite sources are required. The argument uses only small
six-corner matchings and the previously proved common-corner lemmas.
The opposite-target failure catalogue is not a premise.

## 1. Reduction to two multiplicity patterns {.unnumbered}

There are six classes containing a given directed corner. If all six
occur, select nine cubes preserving all six classes and apply
[Argument 24](#arg-24).

If five classes occur, their positive counts, each at most three and
totalling eleven, are exactly

    3,3,3,1,1;  3,3,2,2,1;  3,2,2,2,2.

The latter two contain a 3,2,2,2,1 subpool and are solved by
[Argument 23](#arg-23).

If four classes occur, the counts are 3,3,3,2. At most three classes
cannot accommodate eleven cubes. Thus only 3,3,3,2 and 3,3,3,1,1
remain.

We use an **own loop** to mean a matching of all six tricoloured
corners of a class after reserving two copies of that class. In a
failure, an own-looped triple must use all three of its allowed
repeated colours. Classes **conflict** when reserving one cube of
each with a common repeated colour permits the six-corner completion
of a target whose two poles the reserved cubes supply. Conflicting
classes must have disjoint repeated-colour sets.

An own-loop class conflicts with every present class whose pole pair
intersects its own. To prove this, restore one of the reserved own
class copies, remove the other class's reserved source, and replace
that source in the matching by the restored universal source if
necessary. This is the usual universal-restoration argument.

## 2. Four classes of sizes 3,3,3,2 {.unnumbered}

Normalize the common corner to 01. Write Q={2,3,4}, and put

    P_i=C(0i),    D_i=C({0}∪(Q\{i})).

Arbitrary permutations of Q and interchange of the P and D families
give exactly three forms for a four-class support:

    {P4,D2,D3,D4},
    {P3,P4,D3,D4},
    {P3,P4,D2,D4}.

These correspond to the two missing classes being of one kind,
matched across kinds, or unmatched across kinds.

In each form at least one of the three triples has an own loop.

* For {P4,D2,D3,D4}, at least one of D2,D3 is a triple. If D2 is
  a triple, reserve two copies and match

      D2:32; P4:02,42; D4:31; D3:41,01.

  The case of a D3 triple follows by interchanging 2 and 3.

* For {P3,P4,D3,D4}, at least one of the pairs {P3,D4} and
  {P4,D3} consists of two triples. In the former case, reserve two
  P3 and match

      P3:32; D4:04,31,34; P4:02; D3:01.

  The other pair follows by interchanging 3 and 4.

* For {P3,P4,D2,D4}, both P3 and D2 have own loops already when
  each class has only two copies. The explicit completions are in
  Section 4 of [Argument 35](#arg-35):

      reserve two P3: P4:01,02; D2:31,32; D4:04,34;
      reserve two D2: P3:02,32; P4:41,42; D4:01,31.

  Since only one class is doubled, at least one of P3,D2 is a triple.

Now retain a 3,3,2,2 subpool in which this own-looped class remains
a triple. The common-corner 3,3,2,2 lemma in the same note applies:
it allows the asserted own loop to use any sources of the full pool.
Thus every 3,3,3,2 configuration assembles.

## 3. Five classes of sizes 3,3,3,1,1 {.unnumbered}

Normalize the absent class to D_i. The present classes are

    A=P_i, B=P_j, C=P_k, E=D_j, F=D_k,

where {i,j,k}={2,3,4}. Their poles are 0i,0j,0k,1j,1k, and their
tricoloured corners are:

| Class | Corners |
| --- | --- |
| A | 01,0j,0k,i1,ij,ik |
| B | 01,0i,0k,j1,ji,jk |
| C | 01,0i,0j,k1,ki,kj |
| E | 01,0j,i1,ij,k1,kj |
| F | 01,0k,i1,ik,j1,jk |

Interchanging j,k leaves exactly six choices of the three triples:

    ABC, ABE, ABF, AEF, BCE, BEF.

The following small matching facts close these six cases.

### Own-loop matchings {.unnumbered}

Every row is used after two copies of its target class have been
reserved. The other source multiplicities are as in the specified
triple patterns.

| Looped class | When used | Six-corner completion |
| --- | --- | --- |
| A | Any pattern containing A as a triple | A:i1; E:ij; F:ik; B:0k; C:0j; any unused helper:01 |
| B | ABF or BEF | B:ji; F:j1,jk; A:0k; C:0i; E:01 |
| C | BCE | C:ki; E:k1,kj; A:0j; B:0i; F:01 |
| E | ABE or AEF | E:k1; C:kj; A:0j,ij; F:i1; B:01 |
| E | BCE | E:i1; A:ij; C:0j,k1,kj; B:01 |
| F | BEF | F:i1; A:ik; B:0k,j1,jk; C:01 |

The unused helper in the first row exists: the four helper classes
contain eight cubes in total, and only one from each has been used.
Every helper contains 01. All other rows use at most the stated
counts after the two target copies have been reserved.

### The six cases {.unnumbered}

**ABC.** The class A has an own loop. It therefore conflicts with
B and C, since all three pole pairs contain 0. The classes B,C also
conflict: after reserving one of each, complete a B target by

    B:ji,j1; F:jk; A:0k,01; C:0i.

Thus A requires three repeated colours and B,C require at least one
each, all distinct and all different from 0. Five colours would have
to fit into the four-element set {1,2,3,4}, a contradiction.

**ABE or AEF.** Both A and E have own loops. They conflict via a
B target. After reserving one A and one E, assign

    A:01,0k; C:0i; B:ji,

and fill j1,jk with two remaining B/F sources. This is possible
because B and F have combined multiplicity four, and only one B
has been used. Each remaining B/F source contains j1,jk.
The reserved classes can supply poles 0,j of B. The two triples
would require six different repeated colours, impossible.

**ABF.** Both A and B have own loops. Their poles intersect at 0,
so they conflict by restoration. Their two three-element repeated-
colour sets cannot be disjoint.

**BCE.** Both C and E have own loops. They conflict using a B
target: after reserving one C and one E, match

    B:ji,j1,jk; C:01,0i; A:0k.

The reserved C,E sources supply poles 0,j. Again the two triples
would need six different repeated colours.

**BEF.** Both B and F have own loops. They conflict using a C
target: after reserving one B and one F, match

    E:0j,k1,kj; B:01,0i; C:ki.

The reserved B,F sources supply poles 0,k. The same six-colour
contradiction applies.

All six triple placements are now covered. This proves the
3,3,3,1,1 case and hence the theorem.




# Argument 54: Two opposites and thirteen adjacent cubes in a butterfly {#arg-54}

## Theorem {.unnumbered}

Take thirteen adjacent sources, with at most three in any one
tricoloured-corner class, supported in the butterfly

    A=C01, P=C02, L=C124, M=C123, U=C12, V=C012.

Adding any two opposite sources gives an eight-source five-colour
assembly. The proof uses only the common-corner-eleven lemma and
the explicit assignments below; it does not enumerate inventories.

Write their counts a,p,l,m,u,v. Each is at most three and their
sum is thirteen. An opposite source ab/cd contains both directions
of the four edges between the displayed pairs.

## 1. Four common-corner counts {.unnumbered}

The classes A,L,U,V all contain13; A,M,U,V all contain14;
P,L,U,V all contain23; and P,M,U,V all contain24. If one of
these four subpools has eleven sources, it assembles by
[Argument 53](#arg-53).

We may therefore assume

    a+l ≥3,  a+m ≥3,  p+l ≥3,  p+m ≥3.                (1)

For example, a+l≤2 would leave the common-corner24 subpool
P,M,U,V with at least eleven sources. The other three inequalities
follow in the same way.

The butterfly union misses exactly31,32,41,42. Every opposite
source contains at least one of these four corners. Indeed, if a
four-cycle avoided all four undirected edges between{1,2} and{3,4},
it would lie in the union of the triangles012 and034. A simple
cycle in this graph must lie in one of its triangle blocks, which
cannot contain a four-cycle.

## 2. All four high classes present {.unnumbered}

Suppose a,p,l,m are all positive. By(1), either a,p≥2 or l,m≥2:
otherwise one of a,p and one of l,m would both equal one,
contradicting the corresponding inequality. Also u+v≥1, since
the four high classes can contain at most twelve sources.

The permutation(1 3)(2 4), followed by reversing all directed
cuts, exchanges the two high pairs{A,P} and{L,M} and interchanges
U,V. Thus assume l,m≥2. Select one source K from U or V.
If an opposite O contains31, assemble target03/14 by

    O:31;  P:01;  L:40,43;  M:10,34;  A:04;  K:13.   (2)

Both low classes contain13. Interchanging1,2 and interchanging3,4
preserve the count hypotheses and act transitively on the four
missing corners. Consequently(2) covers every opposite source.
In this case even one of the two opposite sources suffices.

## 3. A high class absent {.unnumbered}

The butterfly symmetries act transitively on the four high classes,
so assume a=0. Equations(1) force l=m=3. The count equation gives

    p+u+v=7,  with 1≤p,u,v≤3.                        (3)

If either opposite O contains31, target03/14 has the assignment

    O:31;  P:01;  L:40,43;  M:10,34;  V:04;  U:13.  (4)

If an opposite contains41, interchange3,4. Thus we may suppose
both opposite sources avoid31 and41, equivalently avoid the
undirected edges13 and14.

There are exactly five such opposite varieties:

| Name | Opposite variety | Missing butterfly corners it supplies |
| --- | --- | --- |
| X | 02/34 | 32,42 |
| Y | 03/24 | 32 |
| Z | 04/23 | 42 |
| R | 02/14 | 42 |
| S | 02/13 | 32 |

To see completeness, if colour1 is omitted, the other four colours
have exactly their three pair partitions X,Y,Z. If colour1 is
present, its two neighbours must be0 and2. The other vertex in its
bipartition class is3 or4, giving S or R.

If the two opposite sources can supply32 and42 using different
sources, use target02/34. Assign those two corners to the opposite
sources,30 to M,40 to L, and03,04,23,24 to four P or V sources.
This is possible because p+v=7-u≥4, and both P and V contain
all four of these forward corners.

Consequently the only pairs left are two sources from{Y,S}, or
two from{Z,R}. Interchanging3,4 exchanges these alternatives.
Consider a pair from{Y,S}.

If at least one source is Y, assign it02, assign the other32,
and use target03/24 with

    Y:02;  other opposite:32;
    P:04;  M:34;  L:40,43,20;  U:23.                 (5)

Thus only two copies of S remain. If p≥2, target02/13 is

    S:12,32;  P:01,21;  M:10,30;  V:03;  U:23,      (6)

where the two S corners use the two distinct opposite sources.
Therefore the sole residual, up to the stated symmetries, is

    p=1; l=m=u=v=3; a=0; two copies of S=02/13.      (7)

Every reduction to(7) has followed from a count inequality, the
five geometrically determined opposite varieties, or an explicit
assembly. No search result is used.

## 4. Repeated colours close the sole residual {.unnumbered}

Recall that the pole pairs of M=C123 and V=C012 are04 and34,
respectively. A source of pole pair ab repeating colour r has
the two bicoloured corners(r,a) and(r,b).

The class M has an own loop: after reserving any two of its three
sources, match its six tricoloured corners by

    remaining M:34;  S:30;  P:24;  L:10,20;  U:14.  (8)

Likewise V has an own loop, with

    remaining V:04;  S:03;  P:24;  L:13,23;  M:14.  (9)

These assignments use only one opposite source each. If two M
sources repeated the same colour, reserve them for M's two
bicoloured target corners and use(8). The analogous construction
using(9) applies to V. Therefore, in a failing pool, the M triple
must use each repeat colour1,2,3 once, and the V triple each repeat
colour0,1,2 once.

Now choose the M source repeating1 for the bicoloured corner(1,0)
and the V source repeating1 for(1,4). Complete the M target by(8),
using an available M source at34. None of its other assignments
uses V, so all eight assigned sources are distinct. This is an
assembly, contradicting failure.

The theorem follows.




# Argument 55: The alternating missing path for 2D+P {#arg-55}

Let

    D=O60={13,14,23,24}, P=O67={01,04,13,34}.

Take two D sources, one P, and eleven adjacent sources of class cap
three, all avoiding the corners32,41,42. The latter directions
alternate along the three-edge path3–2–4–1 in D. We prove assembly.

The eight allowed adjacent classes and their counts are

| Count | Class |
| --- | --- |
| a | A=C(01) |
| b | B=C(02) |
| c | C=C(124) |
| d | E=C(123) |
| e | F=C(12) |
| f | G=C(023) |
| g | H=C(23) |
| h | J=C(012) |

All counts lie between zero and three and sum to eleven. The class
names are used for physical sources; lower-case letters denote their
counts. A triple class has at most one source disjoint from it in a
failure, by the earlier three-opposite/disjoint-source construction.
We also use [Argument 53](#arg-53).

Split according to c, the number of C(124) sources.

## 1. The case c=0 {.unnumbered}

On target O63={03,04,23,24}, put D,D at32,42 and P at40. The five
remaining positions are03,04,23,24,30. The adjacent intersections
are described by the groups

    A:03,04;
    B,J:03,04,23,24;
    E,H:24,30;
    F:23,24;
    G:04,24.

These five positions can be matched whenever

    d+g>0, a+b+h>0, b+h+e>0.                 (1)

Here is the Hall verification. Choose one E/H at30. Put X=b+h
and Y=d+g. On the remaining four positions,03 and23 have
neighbour counts a+X and X+e. The pair03,04 has at least
a+X+f≥2 neighbours because its complementary source groups Y,e
have capacity at most6+3=9. Similarly the pair03,23 has at least
a+X+e≥2 neighbours because Y,f have capacity at most nine. All
other two-position inequalities follow either from these or from
at least ten minus one class neighbours. The only triple not seeing
all ten remaining sources is03,04,23; it sees11−Y≥5. Thus (1)
suffices.

If (1) holds, we have an opposite assembly. Otherwise consider the
three possible zero sums.

### 1.1 a=b=h=0 {.unnumbered}

Only E,F,G,H remain, with eleven sources. All four classes contain
corner24. The common-corner eleven theorem gives an assembly.

### 1.2 b=h=e=0 {.unnumbered}

Only A,E,G,H remain. Their eleven counts have profile3,3,3,2, so
each is at least two. Target O71={01,02,14,24} has the assignment

    D:41,42; P:01; A:02,14; E:10,20; G:24.

### 1.3 d=g=0 {.unnumbered}

Only A,B,F,G,J remain. If a=0, all present classes contain24. If
e=0, all present classes contain04. Either case is covered by the
common-corner theorem.

Assume a,e>0. The counts give

    b+f≥2, a+e+h≥5.

Use target O71 with

    D:41,42; P:10; A:02; F:20;
    two B/G sources:01,24;
    one further A/F/J source:14.

The last source exists after the A,F reservations because at least
five sources lie in those three classes. This completes c=0.

## 2. The case c=1 {.unnumbered}

On O63, D,D again fill32,42. The single C source sees23,40 and
P sees04,40. Thus one of these two sources can fill40 and the other
can be used at either04 or23, according to which source fills40.
For matching purposes the ten remaining adjacent sources therefore
have one extra flexible source on {04,23}.

This gives an assembly whenever

    d+g>0, a+b+h>0.                          (2)

Indeed put one E/H at30. On03,04,23,24, the extra source supplies
04 or23. Corner03 has a+b+h>0 neighbours. Corner24 has at least
nine minus a≥6 adjacent neighbours. The pairs03,04 and03,23
have at least two neighbours, using the extra source. The only
potentially small triple03,04,23 has at least10−(d+g)≥4
neighbours. All other Hall inequalities are automatic from these
counts. If the extra source is assigned04, use P there and C at40;
if it is assigned23, use C there and P at40. If it is unused, put
either eligible source at40 and discard the other.

### 2.1 d=g=0 {.unnumbered}

The other ten adjacent sources are A,B,F,G,J. If a>0, then
b+f>0 because the other three classes have capacity nine. On O71,
assign

    D:41,42; P:10; C:20; A:02;
    one B/G source:01.

The remaining positions14,24 have respectively at least
a+e+h−1≥3 and b+f+e+h−1≥6 unused neighbours, so distinct
helpers fill them.

If a=0, the four counts b,e,f,h sum to ten, so all are positive.
Use P itself as target, with

    D:13,31; P:43; C:40; G:34; F:10; B:01; J:04.

### 2.2 a=b=h=0 {.unnumbered}

The four counts d,e,f,g sum to ten and are all positive. If f≥2,
again use target P:

    D:13,31; P:43; C:40; G:01,04; F:10; H:34.

If f=1, then d=e=g=3. The pool contains the smaller core

    one D +3C(12)+3C(23)+2C(123).

This core assembles by the nine-source union-class lemma: C(12)
and C(23) have the common pole2, their union class is C(123), and
D contains the edge13 joining their other two poles. The lemma's
proof is the main article’s nine-source construction. The singleton
C(124) and C(023) sources are unnecessary.

Thus c=1 is closed.

## 3. The cases c=2 or3 {.unnumbered}

Use P as target. Put D,D at13,31 and two C sources at40,43. If
the other adjacent sources can match any three positions of

    K={01,04,10,34},

P fills the fourth and the target is complete. Their K patterns are

    A,J:{04}; B:{01,04}; E:{10,34};
    F:{10}; G:{01,04,34}; H:{34}.

There are11−c≥8 such sources. If their matching rank is at most
two, König's theorem confines all their patterns to two K positions.
A cover using one corner and one exceptional source would require
at least seven sources at one corner; at most six can be confined
to04, and at most three to any other corner. A cover with only
source vertices is also impossible.

The only two-position sets accommodating eight sources are:

| Positions | Eligible classes besides C |
| --- | --- |
| 01,04 | A,B,J |
| 04,10 | A,F,J |
| 04,34 | A,H,J |
| 10,34 | E,F,H |

The other two pairs admit at most one class. In each displayed row
all three classes occur at least twice, so with C the full adjacent
profile is3,3,3,2.

For the second row, all eleven adjacent sources contain13; for the
fourth, all contain20. The common-corner theorem solves both.

The third row is impossible in a failure: A and H are disjoint,
both have at least two copies, and at least one is a triple. If
both had only two, even three each of C,J would give total only ten.

For the first row, use target O61:

    D:32,41; P:34; A:12,14; B:21; C:43; J:23.

All assignments respect the lower bound of two per class. This
completes c≥2 and hence the alternating-path case.

## Symmetry and scope {.unnumbered}

The other possible single opposite variety in this normalized
alternating five-position cover is O72={02,03,12,13}. Reversing
the path by (1 3)(2 4) and reversing all directed corners preserves
the absent alternating directions and exchanges O67,O72. It also
preserves D. Thus the proof covers both singles, with source class
names permuted accordingly.

The cut list follows directly from the three forbidden directions.
All count reductions and matching criteria above are proved by Hall
and the class caps; no inventory catalogue is used.



# Argument 56: Eliminating four-position Hall covers for 2D+P {#arg-56}

Let the pool contain 2D+P, where D and P are distinct opposite
varieties, and eleven adjacent sources of class multiplicity at most
three. Suppose, for contradiction, that the pool has no assembly.

This note proves that all twelve sources other than D,D have their
D-intersections inside a five-position set H. In particular there
is no four-position cover with one exceptional source. The proof
does not enumerate source inventories.

We use two earlier facts:

* A triple adjacent class has at most one adjacent source disjoint
  from it. Otherwise three copies of the class, two disjoint
  adjacent sources and the three diffuse opposite sources assemble;
  see Section 3 of [Argument 40](#arg-40).
* Nine adjacent cubes cannot all avoid two underlying edges in a
  failure with an opposite source and class cap three. The short
  cut proof is in [Argument 9](#arg-9),
  Section 1, and does not require four opposite sources.

## 1. The initial Hall cover {.unnumbered}

Use D as target. Its two copies are universal. Hence the other twelve
sources have matching rank at most five on its eight positions.
König's theorem gives a set H of corner vertices and some exceptional
source vertices, with total size at most five, covering all incidences.

Each adjacent class meets D in two or four positions. At most two
classes fit in a two-position set, and at most three fit in a
three-position set. These facts are proved in Section 1 of
[Argument 1](#arg-1).

Thus |H|≤2 is impossible: at least five of the eleven adjacent
sources would remain exceptional when |H|=2, exceeding the allowance
of three. Smaller H is still less possible. If |H|=3 and P is
exceptional, at most one adjacent source may be exceptional, whereas
ten do not fit in three positions. If P is contained in H, then H
contains a bidirected edge; a three-position set of that form supports
at most two adjacent classes, hence six copies, again insufficient.

Therefore either |H|=5 and every source is contained in H, or |H|=4
and at most one source is exceptional. We exclude the latter case.
At least ten adjacent sources then have their D-intersections in H.
If P is exceptional, all eleven adjacent sources are contained.

Normalize D={13,14,23,24}. An edge denotes both directions unless
individual corners are listed.

## 2. The ten four-position shapes {.unnumbered}

Up to symmetries of the target and reversal of all directions,
four positions in a bidirected four-cycle have ten shapes. To see
completeness, count complete bidirected edges in H. There are two
forms with two such edges, four forms with one, and four orientations
of the entire four-cycle with none. The adjacent classes whose
D-intersection lies in H are as follows; C(S) means S→Sᶜ.

| H | Eligible outsets S |
| --- | --- |
| 13,14,23,24 | 01;02;124;123;12;012 |
| 13,14,23,31 | 01;124 |
| 13,14,23,32 | 01;124;13;013 |
| 13,14,23,42 | 01;124;14;014 |
| 13,14,31,32 | 01;03;13;013 |
| 13,14,31,41 | 01;234 |
| 13,14,31,42 | 01;14;014 |
| 13,14,32,42 | 01;134;13;14;014;013 |
| 13,24,31,42 | 14;023;23;014 |
| 13,24,32,41 | none |

Each row follows directly by imposing the missing directed-cut
conditions on a two- or three-element outset. Rows with at most
three classes cannot accommodate ten contained adjacent sources.
The ninth row makes at least ten sources avoid the other two
underlying target edges, contradicting the nine-avoider fact.

The fourth and eighth rows contain no complete bidirected edge,
so P is exceptional and all eleven adjacent sources are contained.
Their classes share respectively corner 13 and corner 12. The
common-corner eleven-source theorem in
[Argument 53](#arg-53) solves them.

The first, third and fifth rows remain.

## 3. A directed rectangle containing all eleven adjacent sources {.unnumbered}

In the first row P is exceptional. Write

    A=C(01), B=C(02), C=C(124), E=C(123),
    U=C(12), V=C(012),

with counts a,b,c,e,u,v, each at most three and summing to eleven.
We prove that these sources and D,D assemble; P is unnecessary.

### 3.1 All four star classes occur {.unnumbered}

If a,b,c,e are positive, use target O61={12,14,23,34}. Put D,D at
41,32, and use

    A:12; B:21; C:43; E:34.

Two unused adjacent sources fill 14,23. Among the unused sources,
at least a+e+u+v−2≥3 see 14, and at least b+c+u+v−2≥3 see 23.
Two distinct sources can therefore be chosen.

### 3.2 Some star class is absent {.unnumbered}

The symmetries interchanging 1,2, interchanging 3,4, and reversing
directions while interchanging the two parts of D act transitively
on A,B,C,E. Assume a=0.

If c,e>0, use target O63={03,04,23,24}. Put D,D at32,42, C at40,
and E at30. The B/V sources are universal on 03,04,23,24. Their
number satisfies b+v≥2, since c+e+u≤9 and the total is eleven.
Use two of them at03,04. The remaining adjacent neighbours of23
number at least b+v+c+u−3=8−e≥5; those of24 number at least
b+v+e+u−3=8−c≥5. Thus two further distinct sources fill23,24.

Otherwise one of C,E is absent as well. There cannot be three
absent stars, since the three remaining classes would have total
capacity nine. We are left with one A/B star, one C/E star, and
U,V. All four counts are at least two and exactly three are three.
Normalize the support to A=C(01), C=C(124), U=C(12), V=C(012).

### 3.3 The four-class residual {.unnumbered}

Both U and V have own loops already when all four counts are two:

    reserve two U: A:13,14; C:10,20; V:23,24;
    reserve two V: A:03,04; C:13,23; U:14,24.

The own-loop restoration argument gives the conflict edges A–U and
C–V, whose pole pairs intersect. Three further edges have the
following completions, after the indicated pair is reserved:

| Reserved pair | Target class | Tricoloured completion |
| --- | --- | --- |
| A,V | C | C:40,43; A:13; U:10,20; V:23 |
| C,U | A | A:02,12; V:03,04; C:13; U:14 |
| U,V | C(14) | C:40,43; A:12,13; D:42; U:10 |

If U,V are both triples, their conflicting three-element repeat
sets would require six colours. If U is doubled, V is a triple and
the conflict triangle U,V,A requires at least 2+3+1=6 colours.
If V is doubled, use the triangle U,V,C instead. These exhaust
the possible positions of the unique double. Thus the first row
is completely excluded.

## 4. The row H={13,14,23,32} {.unnumbered}

The contained classes are

    A=C(01), B=C(124), C=C(13), E=C(013).

The classes B,E are disjoint. If all eleven adjacent sources were
contained, their counts would be 3,3,3,2. At least one of B,E would
then be a triple with at least two disjoint sources, impossible.

Consequently P is contained and ten adjacent sources are contained.
Retain ten if necessary. All four contained classes occur, since
any three have capacity nine. The only possible P are

    O64={02,04,23,34}, O73={01,03,12,23}.

For P=O64, use target O63 and assign

    D:24,42; P:23; A:03; B:40; C:30.

The remaining positions04,32 are filled by two remaining sources
from A,C,E. At least a+c+e−2=8−b≥5 such sources remain. Each meets
04 or32, and E supplies both, so a two-position matching exists.

For P=O73, use target O61 and assign

    D:23,41; P:21; B:43;
    four C/E sources:12,14,32,34.

The C/E sources are universal on those four positions and c+e≥4,
because a+b≤6. Both possibilities therefore assemble.

## 5. The row H={13,14,31,32} {.unnumbered}

The contained classes are

    A=C(01), B=C(03), C=C(13), E=C(013).

### 5.1 P is contained {.unnumbered}

The only choices are P=O67={01,04,13,34} or
P=O72={02,03,12,13}. At least ten adjacent sources are contained;
retain ten. All four classes are positive.

For P=O67, target O66={03,04,13,14} has the assignment

    P:40; D:13,41; A:03; B:31; C:30.

The two remaining positions04,14 are filled by unused adjacent
sources. Seven remain, each meeting04 or14, and E supplies both.
Thus two distinct sources suffice.

For P=O72 and c≥2, use target O73={01,03,12,23}:

    P:21; D:23,32; A:03; B:01; C:10,30; E:12.

If c=1, the other three counts are all three. Use target
O74={01,02,13,23} instead:

    P:20; D:23,31; C:10; B:01; A:02,13; E:32.

### 5.2 P is exceptional {.unnumbered}

Now all eleven adjacent sources are contained, with counts3,3,3,2.
Whenever A is a triple it has an own loop, using

    A:03; D:13; B:02,04; C:12,14

after two A reservations. Likewise a B triple has an own loop via

    B:01; D:31; A:02,04; C:32,34.

The class E has an own loop already at counts two in the other
classes, using A:02,04; B:32,34; C:12,14.

If A and B are both triples, their own loops conflict at the common
pole0 and give an assembly. Otherwise the unique double is one of
A,B; the other and E are both looped triples. Their conflict edges
are witnessed as follows:

| Reserved pair | Target | Tricoloured completion |
| --- | --- | --- |
| A,E | C(034) | B:01,31; A:02; D:41,42; C:32 |
| B,E | C(012) | A:03,13; B:04; D:23,24; C:14 |

Again two conflicting triple classes would require six repeated
colours, impossible.

Every four-position cover is now excluded. By Section 1, failure
forces a five-position set H containing the D-intersections of P
and of all eleven adjacent sources. Equivalently, three target
positions are absent from P and the entire adjacent pool.



# Argument 57: Five-position covers with a missing bidirected edge {#arg-57}

Keep the setting of [Argument 56](#arg-56): the pool consists of
2D+P, D≠P, and eleven adjacent sources with class cap three. In a
hypothetical failure, every adjacent triple has at most one adjacent
source disjoint from it. The preceding note reduces failure to a
five-position set H containing the D-intersections of P and all
eleven adjacent sources.

This note closes the cases where the three omitted D positions
include both directions of an edge. It follows in particular that
the whole neighbouring pair case is solved.

Normalize D={13,14,23,24}. The omitted set consists of a bidirected
edge and a further directed corner. There are exactly two geometries,
according as their underlying edges meet or are disjoint.

## 1. The two edges meet {.unnumbered}

Normalize the omitted corners to24,42,41. The containing set is

    H={13,14,23,31,32}.

The adjacent cuts avoiding those three corners are exactly

    A=C(01), B=C(03), C=C(124), E=C(13), F=C(013).

Write their counts as a,b,c,e,f. They sum to eleven and are at most
three. The class C is disjoint from B and F.

If c=3, the disjoint-source bound gives b+f≤1, whence the total
is at most3+3+3+1=10. Thus c≤2. If c=0, all eleven adjacent
sources have their D-intersections in {13,14,31,32}; Section 5.2
of [Argument 56](#arg-56) gives an assembly using D,D alone.

Suppose c>0. All five classes occur. For c=1, the other four
counts sum to ten, forcing all four positive. For c=2, neither B
nor F may be a triple, since either would have two disjoint C
sources. Hence b,f≤2. Omitting B or F would give total at most
3+3+2+2=10; omitting A or E gives an even smaller bound. Again all
four other classes are positive.

Use target O66={03,04,13,14}, with

    D:13,41; A:03; B:31; C:40; E:30.

Two more adjacent sources fill04,14. At least

    a+b+e+f−3 = 8−c ≥ 6

unused sources from A,B,E,F remain, and each meets04 or14. A
remaining F sees both, so two distinct sources can fill the pair.
This proves the case. P is unnecessary in the displayed assembly.

## 2. The two edges are disjoint {.unnumbered}

Normalize the omitted corners to24,42,31, so

    H={13,14,23,32,41}.

The eligible cuts are

    A=C(01), B=C(124), C=C(13),
    E=C(024), F=C(24), G=C(013).

Let their counts be a,b,c,e,f,g, with sum eleven and cap three.
Put

    x=c+g, y=e+f, L=a+x, R=b+y.

The class F is disjoint from every class in the left group
{A,C,G}, while G is disjoint from every class in the right group
{B,E,F}. We first show

    x>0, y>0, L≥3, R≥3.

If x=0, only A,B,E,F remain. Their eleven cubes have counts3,3,3,2.
The disjoint classes A,F each have at least two cubes and at least
one is a triple, contradicting the disjoint-source bound. Similarly,
y=0 leaves A,B,C,G and the disjoint pair B,G, giving a contradiction.

If L≤2, then R≥9. The three right classes have cap three, so
R=9, L=2 and b=e=f=3. The F triple has two disjoint left sources,
again impossible. Interchanging the roles gives R≥3 as well: if
R≤2, then a=c=g=3 and the G triple has two disjoint right sources.

Now use target O61={12,14,23,34}. Its adjacent intersections split
into two four-position halves:

| Source group | Available positions |
| --- | --- |
| A | 12,14 |
| C,G | 12,14,32,34 |
| B | 23,43 |
| E,F | 21,23,41,43 |

Put the two D copies at32,41. Since x>0 and L≥3, choose one C/G
source at34 and two further A/C/G sources at12,14. Since y>0
and R≥3, choose one E/F source at21 and two further B/E/F sources
at23,43. These eight assignments are compatible and use distinct
physical cubes. Again P is unnecessary.

Both missing-bidirected-edge geometries therefore assemble.

## 3. Consequence: the neighbouring profile 2,1 is closed {.unnumbered}

If D and P share two underlying edges, their D-intersection consists
of two complete bidirected edges. A five-position containing set H
must contain those four positions. Its three-position complement
therefore consists of one complete bidirected edge and one further
directed corner. Sections 1 and 2 exclude it.

Combining with [Argument 56](#arg-56) proves:

> Two copies of one opposite variety D and one copy of a distinct
> neighbouring variety P, together with eleven adjacent cubes of
> class cap three, always assemble a five-colour target.

For a nonneighbouring P, the only cases still left after these
reductions have three omitted corners on three distinct underlying
edges. These edges form the three-edge path complementary to D∩P
inside D. Under symmetries of D, the three omitted directions have
three patterns: monotone, one change, and alternating. In using this
normalization one must retain both possible choices of P sharing
the remaining edge: path reversal need not preserve the marked
single variety P. Equivalently, after fixing the ordered pair D,P,
direction reversal leaves four oriented path cases, with the two
one-change forms distinguished.



# Argument 58: The one-change missing path for 2D+P {#arg-58}

Normalize D={13,14,23,24}. Suppose the eleven adjacent sources,
each class of multiplicity at most three, avoid24,31,41. These
directions have one change along the three-edge path2–4–1–3.

The eligible classes, with their counts, are

| Count | Class |
| --- | --- |
| a | A=C(01) |
| b | B=C(134) |
| c | C=C(124) |
| e | E=C(13) |
| f | F=C(14) |
| g | G=C(014) |
| h | H=C(013) |

The opposite sources are D,D,P. Containment in the corresponding
five-position D-cover forces P to be one of

    O64={02,04,23,34}, O73={01,03,12,23}.

Both choices are treated separately, so no symmetry of the marked
single variety is assumed. We use the common-corner eleven-source
theorem in [Argument 53](#arg-53).

## 1. P=O64 {.unnumbered}

In target P, the two D copies can fill23,32. Consider its other six
positions

    R={02,04,20,34,40,43}.

If the adjacent sources match any five of R, use P at the sixth and
the two D copies at23,32. Thus failure implies adjacent matching
rank at most four on R. The adjacent patterns on R are

| Class | R pattern |
| --- | --- |
| A | 02,04 |
| B | 40 |
| C | 20,40,43 |
| E | 34 |
| F | 40,43 |
| G | 02,43 |
| H | 02,04,34 |

Any one, two or three positions of R contain patterns from at most
one, two or three of these classes, respectively. For the only
nontrivial bound, a three-position set containing C's pattern admits
just B,C,F, while one containing H's admits just A,E,H. Otherwise
C,H are excluded. Among A,F,G, the pairs A,F have four positions
in union; A,G have three but contain neither singleton position;
F,G have three and contain only B's singleton position. Hence a
three-position set still admits at most three classes.

König's theorem now shows that all eleven patterns lie in a
four-position set. Indeed a cover with k≤3 corner vertices and
at most4−k source vertices covers at most3k+(4−k)≤10 copies.

Equivalently, two R positions are absent from the entire adjacent
pool. The only such absences leaving capacity at least eleven are
the six rows below. Every row has four eligible classes, necessarily
with profile3,3,3,2.

| Missing R positions | Eligible classes |
| --- | --- |
| 04,20 | B,E,F,G |
| 20,34 | A,B,F,G |
| 20,40 | A,E,G,H |
| 20,43 | A,B,E,H |
| 02,04 | B,C,E,F |
| 04,34 | B,C,F,G |

This table follows directly from the seven patterns above: every
other missing pair leaves at most three eligible classes.

The fifth row has all eleven sources through corner10, so the
common-corner theorem solves it. Each other row admits target
O63={03,04,23,24} with the explicit assignments below. Every
adjacent class is used at most twice, within its guaranteed count.

| Eligible classes | Eight-corner assignment |
| --- | --- |
| B,E,F,G | G:03; P:04; D:23,24; B:40,42; E:30,32 |
| A,B,F,G | A:03,04; P:23; D:24,42; B:30,32; F:40 |
| A,E,G,H | A:03,04; P:40; D:23,24; E:30,32; G:42 |
| A,B,E,H | A:03,04; P:23; D:24,42; B:32,40; E:30 |
| B,C,F,G | G:03; P:04; D:24,42; B:30,32; C:23,40 |

Thus P=O64 always assembles.

## 2. P=O73 {.unnumbered}

Use target O61={12,14,23,34}. Put P at21 and one D at41. The
remaining D source sees14,23,32. The adjacent intersections on the
other six positions are

| Source group | Positions |
| --- | --- |
| A | 12,14 |
| B | 12,32 |
| C | 23,43 |
| E,H | 12,14,32,34 |
| F,G | 12,43 |

Put x=e+h and y=f+g. This target assembles whenever

    x>0 and c+y>0.                            (1)

For clarity, these are sufficient by the following full Hall
check. Any set containing12 has at least11−c≥8 adjacent neighbours.
For sets inside {14,23,32,34,43}, corner34 has x neighbours and
corner43 has c+y. The remaining D source meets14,23,32. The only
additional inequalities not immediate from (1) and the total count
are

    a+b+x≥2, a+c+x≥2, b+c+x≥2.

These hold because their respective complementary groups c+y,
b+y,a+y have capacity at most3+6=9, while the total is eleven.
All four-position sets have at least12−y≥6 neighbours or at
least12 minus one class; the five-position set meets all sources.
Thus every Hall inequality holds.

If c+y=0, only A,B,E,H occur, and all their sources contain12.
The common-corner theorem applies.

It remains x=0, so E,H are absent. The five possible classes are
A,B,C,F,G, with total eleven. If b=0, all present classes contain13.
If c=0, all contain12. Again the common-corner theorem applies.

Assume b,c>0. Since b+c+f≤9, there are at least two A/G sources.
Use target O72={02,03,12,13}, with

    D:13,31; P:21; C:20; B:30;
    two A/G sources:02,03;
    one further A/B/F/G source:12.

The last source exists: the four indicated classes have11−c≥8
copies, and only three have been used. Every such class contains12.
This completes the P=O73 case.

Both one-change configurations are therefore soluble, by explicit
geometric and count arguments rather than inventory enumeration.



# Argument 59: The star-and-triangle family with two opposite cubes {#arg-59}

**Theorem.** Take two arbitrary opposite-repeat cubes, with no
restriction on whether their varieties coincide, and thirteen
adjacent-repeat cubes. Suppose every adjacent tricoloured-corner
class occurs at most three times, and all adjacent classes belong to

    C(01), C(02), C(03), C(04), C(034), C(024), C(014).

Then the pool contains an eight-cube assembly of a five-colour target.
The same statement holds after any colour permutation or simultaneous
reversal of all directed corners.

The proof uses the common-corner eleven-source theorem from
[Argument 53](#arg-53) and the nine-source construction in
the main article’s nine-source construction.
All other steps are direct constructions or a six-position Hall
argument. No inventory search is a premise.

## 1. Notation and the common-corner reduction {.unnumbered}

Let I={1,2,3}, and write

    P_i=C(0i), R=C(04), Q_i=C(04i)    (i in I).

Their multiplicities are p_i,r,q_i, respectively. Each lies between
zero and three, and

    p_1+p_2+p_3+r+q_1+q_2+q_3=13.

Put s_i=p_i+q_i and p=p_1+p_2+p_3. The two opposite sources are
O_1,O_2. An opposite source supplies both directions of every edge
of its four-cycle. We write {a,b}|{c,d} for the opposite target whose
underlying edges join these two pairs.

Every class except P_i,Q_i supplies corner0i. Consequently s_i≤2
would give at least eleven adjacent sources with common corner0i,
which assemble by the common-corner theorem. For the remainder,
suppose the pool fails. Then

    s_i≥3 for every i in I.                              (1)

Also p≥1, because the four classes R,Q_1,Q_2,Q_3 have total
capacity twelve.

## 2. A positive class and an opposite edge {.unnumbered}

**Lemma.** Under (1), suppose p_j>0 and an opposite source O supplies
edge4k, where j,k are distinct members of I. Then the pool assembles.

Let i be the third member of I. Use target {4,i}|{j,k}. Put one P_j
source atj4 and O atk4. The other six target positions are

    ij, ik, ji, ki, 4j, 4k.

They will be filled entirely by the twelve remaining adjacent
sources. Define the three disjoint source groups

    G_i = all P_i and Q_i sources;
    G_j = all P_j and Q_j sources after the P_j reservation;
    G_k = all P_k and Q_k sources.

Their sizes are s_i,s_j−1,s_k, hence at least3,2,3, respectively.
The complete neighbourhoods of the six positions are

| Positions | Adjacent-source neighbourhood after the reservation |
| --- | --- |
| ij, ik | G_i |
| ji | G_j |
| ki | G_k |
| 4j | R, Q_i, Q_k |
| 4k | R, Q_i, Q_j |

Here a class name denotes all its available copies. In particular,
the reservation of P_j changes neither of the last two rows.

We check Hall's condition for every subset of these six positions.
Call ij,ik,ji,ki the first four positions and 4j,4k the last two.

* A subset containing no first position consists of one or both last
  positions. Each last position has at least one neighbour: for
  example, if r=q_i=q_k=0, only P_1,P_2,P_3,Q_j could occur, whose
  total capacity twelve contradicts the original count thirteen.
  The two last positions together have

      r+q_1+q_2+q_3=13−p≥4

  neighbours.

* If the subset meets at least two of the three first-position
  groups {ij,ik}, {ji}, {ki}, their disjoint source groups alone
  supply at least five neighbours. A subset meeting exactly two
  groups has at most five positions. A subset meeting all three
  groups has at most six positions and at least3+2+3=8 neighbours.

* Suppose the subset meets only {ij,ik} among the first-position
  groups. If it uses at most one last position, it has at most three
  positions and at least s_i≥3 neighbours. If it uses both last
  positions, its neighbour count is

      s_i+r+q_j+q_k=13−p_j−p_k≥7.

* Suppose the subset meets only {ji}. With at most one last position
  it has at most two positions and at least s_j−1≥2 neighbours. With
  both last positions it has

      (s_j−1)+r+q_i+q_k=12−p_i−p_k≥6

  neighbours. If it meets only {ki}, the same argument uses s_k≥3
  and, when both last positions occur,

      s_k+r+q_i+q_j=13−p_i−p_j≥7.

This exhausts the subsets. The six-position matching, together with
the two reserved sources, proves the lemma.

For any opposite source O put

    N_4(O)={k in I : O supplies edge4k}.

Since p≥1, the lemma implies the following restriction in a failure:
either N_4(O) is empty, or it is a singleton {s} and every positive
P_j is P_s. Indeed, two members of N_4(O) would give a member
different from any chosen j with p_j>0. Moreover N_4(O) is empty
exactly when O omits colour4. If N_4(O)={s}, the two neighbours of4
in O are0,s.

## 3. Two different non-4 neighbours of0 {.unnumbered}

**Lemma.** Under (1), suppose O_1,O_2 can be assigned to edges0i,0k
for two distinct i,k in I. Then the pool assembles.

Let j be the third member of I and use target {0,j}|{i,k}. Put the
opposite sources ati0,k0. The remaining six positions are filled as
follows:

| Sources | Assigned corners |
| --- | --- |
| Two sources from P_j,Q_j | ji, jk |
| Two sources from P_i,Q_i | ij, 0k |
| Two sources from P_k,Q_k | kj, 0i |

Every source in a row supplies both listed corners. Each row has at
least three sources by (1), so all six chosen sources are distinct.
This proves the lemma.

Now apply both lemmas to a hypothetical failure. An opposite source
omitting4 has two neighbours of0 in I. Any other opposite source
allowed by Section 2 either also omits4, or has neighbours0,s at4
and therefore has a further neighbour t in I at0. In either case
the two sources can be assigned to distinct edges0i,0k. Thus neither
opposite source can omit4 in a failure.

Both N_4(O_1),N_4(O_2) are therefore singletons. Since some P_j
occurs, they must have the same member s, and only P_s can occur.
Each opposite has a further neighbour t in I at0. These two
neighbours must coincide, by the second lemma. Also t≠s, since the
four-cycle has edges04,4s and cannot close using only three vertices.
Both opposite sources are consequently the same four-cycle

    O={04,4s,st,t0}.                                      (2)

Let u be the third member of I.

## 4. The last multiplicity reduction {.unnumbered}

We have p_t=p_u=0. Since s_t,s_u≥3 and each class has cap three,

    q_t=q_u=3.

The remaining count equation is

    p_s+r+q_s=7,      1≤p_s≤3, r≤3, q_s≤3.               (3)

In particular q_s≥1.

If p_s≥2, use the opposite target {0,s}|{4,t}. There is the explicit
assembly

| Sources | Assigned corners |
| --- | --- |
| The two O sources | 40, t0 |
| Two P_s | 04, s4 |
| One Q_t | ts |
| One Q_s | st |
| Two Q_u | 0t, 4s |

The eight corners are distinct and are exactly those of the target.
The indicated source multiplicities are available by (3), and every
incidence follows directly from the relevant cut or from (2).

Therefore a failure would require p_s=1. Equation (3) then forces
r=q_s=3. The whole pool has the form

    2O + P_s + 3R + 3Q_s + 3Q_t + 3Q_u,                 (4)

with O given by (2).

## 5. The repeated-colour completion {.unnumbered}

The nine-source subpool

    O + 3Q_s + 3Q_t + 2R

already assembles. Indeed, O supplies edgest. Simultaneous reversal
sends

    Q_s=C(04s) to C(tu),
    Q_t=C(04t) to C(su),
    R=C(04)   to C(stu),

and leaves the bidirected corners of O unchanged. Thus the reversed
subpool is precisely the previously proved nine-source construction

    O(edge st) + 3C(tu) + 3C(su) + 2C(stu).

This contradicts failure in (4) and proves the theorem. Equivalently,
Q_s and Q_t are own-looped triples with intersecting pole pairs tu
and su, so their repeated colours give the completion.

## 6. Proof dependencies and scope {.unnumbered}

The proof is uniform in the two original opposite varieties and in
all actual repeated colours within every adjacent class. It assumes
only the cap of three on adjacent tricoloured-corner classes.

Its two earlier inputs are:

1. the theorem that eleven adjacent sources with a common directed
   tricoloured corner and class cap three assemble;
2. the nine-source union-class construction, including simultaneous
   reversal.

Both inputs have independently audited hand proofs. The two new
matching lemmas and the multiplicity reduction above have passed
independent root and alternative-agent mathematical audits. The latter
is recorded in the proof-development record.
No exhaustive search or new formalisation is used.



# Argument 60: Three opposite cubes with one doubled variety {#arg-60}

**Theorem.** Let D,P be distinct opposite-repeat five-colour varieties.
Two copies of D, one of P, and eleven adjacent-repeat cubes of
tricoloured-corner class multiplicity at most three contain an
eight-cube assembly of a five-colour target.

This note joins the component hand proofs. The proof does not use
the exhaustive fourteen-cube failure catalogue.

## 1. Reduction to a five-position cover of D {.unnumbered}

Suppose the pool fails. A triple adjacent class has at most one
adjacent source disjoint from it: the earlier construction using
three diffuse opposite sources, the triple and two disjoint sources
would otherwise assemble.

On target D its two copies are universal, so the other twelve sources
have matching rank at most five. The argument in
[Argument 56](#arg-56) excludes every König cover with fewer than
five corner vertices, including the four-corner cover with one
exceptional source. Consequently all twelve D-intersections lie in
a five-position set H.

If the complement of H contains a complete bidirected edge,
[Argument 57](#arg-57) gives an assembly. This already
settles neighbouring varieties D,P: their four-position intersection
is two complete edges, so a five-position H containing it necessarily
has a missing complete edge.

## 2. The remaining three oriented-path forms {.unnumbered}

Only the nonneighbouring case remains. The complement of H consists
of three positions on distinct underlying target edges. These three
edges form the path obtained by deleting the common edge D∩P from
D. The cut restrictions have three geometric forms, up to target
symmetries and simultaneous reversal of directions.

Normalize D={13,14,23,24}. The following table records the three
forms, with every possible single P retained. Thus reversal of the
path is not incorrectly assumed to preserve the marked variety P.

| Form | Absent D corners | Eligible adjacent outsets | Possible P |
| --- | --- | --- | --- |
| Monotone | 24,32,41 | 01;124;14;014 | O67,O72 |
| One change | 24,31,41 | 01;134;124;13;14;014;013 | O64,O73 |
| Alternating | 32,41,42 | 01;02;124;123;12;023;23;012 | O67,O72 |

The cut lists follow by imposing that each absent direction u→v
forbids u in the outset with v outside it. The possible opposite
singles are obtained by closing a four-cycle meeting D only in
the remaining bidirected edge. There are exactly two choices per
edge, listed above.

In the monotone row, all eleven adjacent sources contain corner13.
The elementary theorem in [Argument 53](#arg-53) therefore
gives an assembly without using any opposite source.

Both singles in the one-change row are covered separately by
[Argument 58](#arg-58).

The alternating row is covered by [Argument 55](#arg-55).
Its proof handles P=O67. The colour permutation (1 3)(2 4), followed
by reversing all directions, preserves that absent alternating
pattern and D, and exchanges O67 with O72. It therefore covers the
other single as well.

All possible five-position covers have now been excluded. This
proves the theorem.

## 3. Dependency and status {.unnumbered}

The proof uses the earlier three-opposite/disjoint-source construction,
the two- and three-position cut bounds, the nine-avoider observation,
and the following new component notes:

- [Argument 53](#arg-53);
- [Argument 56](#arg-56);
- [Argument 57](#arg-57);
- [Argument 58](#arg-58);
- [Argument 55](#arg-55).

The last alternating count configuration uses the independent
nine-source construction in the main article’s nine-source construction.


# Argument 61: Three distinct opposite sources when an edge is absent from the adjacent pool {#arg-61}

**Lemma.** Three pairwise distinct opposite varieties, together with
eleven adjacent sources whose tricoloured-corner class counts are at
most three, contain an opposite assembly if the adjacent sources all
avoid both directions of any one underlying edge.

There is no condition on whether the opposite varieties contain the
avoided edge. The proof uses no inventory enumeration.

Normalize the avoided edge to 01. Its adjacent avoiders are exactly

    X=C(01), X_i=C(01i), i=2,3,4,

and their reverses. Call these the forward and backward groups. On
the forward grid

    02 03 04
    12 13 14,

X has all six positions, while X_i omits column i and contains both
other columns. An opposite source has either a two-column rectangle
or two positions in different columns; its pattern determines its
variety uniquely.

## 1. Three opposite sources and one full-column helper {.unnumbered}

**Grid lemma.** Add to the three distinct opposite grid patterns a
helper B whose grid pattern is the full grid or a two-column rectangle.
These four sources match a two-column rectangle, unless the three
opposite patterns are precisely the three pairs on three positions,
one in each column.

The full-grid matching rank is four. Source-side Hall is immediate
for subsets containing B, whose pattern has at least four positions.
Three distinct opposite patterns have union at least three, and
every one has size at least two.

Suppose no rectangle can be matched. Let M be the rank-four
transversal matroid on the six positions, and let N be its rank-two
dual. The pairs of holes that can be omitted are the bases of N.
Every same-column pair is a nonbasis. Write H for the nonloop set
of N. Alternating paths from the two holes give

    |N_sources(H)|=|H|−2.

For |H|=2, no source meets H. But its two positions belong to
different columns, since they form a basis of N; B cannot avoid
two positions in different columns. For |H|=4, B meets H, leaving
two opposite sources whose patterns are contained in the other two
positions. They would be the same variety. For |H|=5, one source
would have its pattern in the single remaining position. These
three sizes are impossible.

Suppose |H|=6. Every column's two positions are parallel in N.
The parallel classes are either the three columns separately, or
two columns together and the third separately.

In the three-class case, a two-position opposite pattern would be a
basis of N, so its complement would be matchable by all four sources
while containing no position for that opposite source. Hence all
three opposite patterns must be the three distinct rectangles.
On any rectangle, one of them and B can be taken universal by
choosing B's rectangle if B is not full; the other two opposite
sources each occupy a different whole column. They match the four
positions directly, a contradiction.

In the two-class case, let V be the single-column parallel class
and U the other four positions. Dual rank gives r_M(V)=1. There
are no M loops, because N has no coloops: each of its parallel
classes has at least two positions. Thus both positions of V are
supported, and precisely one source R meets V, containing both.
If R is opposite, it is a rectangle; B then avoids V and equals U.
If R=B, the other three sources are opposite patterns inside U.
In either case all four restrictions to U have size at least two,
their union is U, and no three restrictions lie in two positions.
For the last assertion, the opposite two-position patterns are
distinct and use different columns, whereas the restriction of a
rectangle crossing V is a single column. Hall therefore matches U,
again a contradiction.

The only remaining size is |H|=3. B meets H, so all three opposite
patterns lie in its three-position complement. A three-position
shape in two columns contains only two possible opposite patterns.
Thus the complement has one position in each column, and the
three opposite patterns are its three pairs. This proves the grid
lemma. These three varieties form a line.

## 2. A forward pool with two copies of each class {.unnumbered}

**Allocation lemma.** Three distinct opposite sources together with
two copies of each of X,X_2,X_3,X_4 contain an opposite assembly.

Among the three opposite sources choose two, U,V, and an endpoint
a of 01 such that U and V can supply incoming corners ia and ja
for different i,j in {2,3,4}. Here is why this is always possible.

Two distinct opposite varieties fail this selection only when one
omits 0 and the other omits 1. Otherwise they share an endpoint a.
If either has two neighbours of a among 2,3,4, distinct i,j can be
chosen. If both have only one such neighbour at both endpoints,
both contain 01. Their neighbours of 0 and 1 outside 01 determine
the whole four-cycle, so two distinct varieties differ at one of
these endpoints. That endpoint gives different i,j. Three distinct
varieties cannot have every pair of the exceptional omission form.

Let k be the remaining colour in {2,3,4}, and use the opposite
target with parts {a,k} and {i,j}. Put U,V at ia,ja. Its other six
positions are filled by

    X: ai,aj;  X_k: ki,kj;  X_i: ik;  X_j: jk.

Every required class count is at most two. This proves the lemma.

## 3. Both orientations occur {.unnumbered}

Choose the majority orientation as forward. It contains at least
six sources. On every high target with parts 01 and two of 2,3,4,
four forward sources match the whole forward rectangle. Each source
meets either both columns or one full column, and at most three
forward sources miss a specified column. Both columns therefore
have at least three source neighbours; Hall gives the four matches.

Choose one backward source B and identify its reverse grid with the
forward grid. If the grid lemma gives a four-source rectangle
matching, combine its three opposite sources and B on the backward
half with four forward sources on the forward half. This assembles
an opposite target.

It remains that the three opposite patterns are the three pairs on
one position in each column.

### At least two backward sources {.unnumbered}

Choose any two of them. Each has both positions in at least two
columns. Choose different columns i,j that they respectively meet,
and consider the rectangle on i,j. Put the two backward sources
in the positions complementary to the line's distinguished position
in each column. Two distinct line sources match the two distinguished
positions, because each position belongs to two of the three line
patterns. Four forward sources fill the other directed half.

This uses only two opposite sources and six adjacent sources.

### Exactly one backward source {.unnumbered}

There are ten forward sources. All four forward classes occur,
since three classes have capacity nine. Write their counts as
x,x_2,x_3,x_4. If x=1, then x_2=x_3=x_4=3; otherwise x≥2.

Up to permuting columns and interchanging the two endpoints, the
three distinguished positions have two possible shapes.

If all lie in one row, normalize them to 12,13,14. The three
opposite sources are the line of four-cycles on 1,2,3,4. Choose
k with x_k≥2, and let i,j be the other two column colours. Two
line sources can fill i1,j1 on target {1,k}|{i,j}. The remaining
six positions have the allocation in Section 2. If x≥2, use it
as written. If x=1, use an extra X_j for 1i and an extra X_i for
1j instead of the two X sources; both classes have count three.

For the mixed-row shape, normalize the distinguished positions to
02,13,14. The opposite varieties are

    O60={13,14,23,24},
    O71={01,02,14,24},
    O74={01,02,13,23}.

Use target O60. The opposite sources fill

    O74:31; O71:41; O60:23.

The adjacent sources fill

    X:13,14; X_2:24; X_3:32; X_4:42.

If x=1, replace the two X assignments by an extra X_4 at13 and
an extra X_3 at14. Both classes then use two of their three copies.
Thus this line shape is solved as well.

The sole backward source need not be used in these last constructions.

## 4. All sources have one orientation {.unnumbered}

There are eleven forward sources in four classes of cap three, so
every class has at least two copies. The allocation lemma of
Section 2 applies directly.

All orientation cases have been covered, proving the stated
global-zero-edge lemma.




# Argument 62: Three distinct high opposite sources and a one-sided rectangle family {#arg-62}

**Lemma.** Suppose three distinct opposite varieties each meet at
least two underlying edges of T=01|23. Suppose eleven adjacent
sources, with class cap three, have all their T-corners in the
forward half 01→23. Then the pool assembles a five-colour target.

The union of the opposite sources need not cover all edges of T.
This stronger scope is useful for the unsupported common-target
case as well.

The six possible adjacent classes are

    A=C(01), B=C(014),
    P=C(04), Q=C(14), R=C(012), S=C(013).

Write their counts as a,b,p,q,r,s. Their sum is eleven and each
count is at most three. The list follows directly by intersecting
each cut with the square T, or by choosing the side of the fifth
colour after prescribing the four square vertices.

We use two previously proved lemmas:

- [Argument 61](#arg-61): three distinct opposite sources and eleven
  capped adjacent sources avoiding an underlying edge assemble;
- [Argument 53](#arg-53): eleven
  capped adjacent sources sharing one directed corner assemble.

## 1. Only three or four peripheral classes need consideration {.unnumbered}

Only P,Q contain the underlying edge 01, and only R,S contain 23.
If either pair of classes is absent, the global-zero-edge lemma
applies. Thus at least one class from each pair occurs.

If there is just one from each pair, all occupied classes share a
directed corner of T. For example A,B,P,R all contain03; the other
choices are obtained by interchanging 0,1 or 2,3. The common-corner
lemma applies.

It remains that three or four of P,Q,R,S occur. The symmetries
interchanging 0,1, interchanging 2,3, and reversing all directions
while exchanging the two parts of T allow the three-class case
to be normalized to p,q,r>0 and s=0.

## 2. All four peripheral classes occur {.unnumbered}

Partition the four edges of T into the two disjoint pairs

    E={02,13}, F={03,12}.

Three distinct high opposite varieties collectively cover at least
three edges of T: a fixed two-edge intersection determines its
opposite variety uniquely, and the variety T itself covers all four.
Hence at least one of E,F is entirely supported by the three sources.

Any two target edges have at least two opposite-source neighbours,
since at most one of the three distinct high varieties can have
its whole intersection in the complementary pair. Therefore two
opposite cubes can fill the two reverse directions on the supported
pair. Use E, say, so these positions are20,31, and take target

    U={01,02,13,23}.

Put P at01, Q at10, R at23, and S at32. The only positions left
are02,13. Every one of the seven remaining adjacent sources meets
this pair: A,B meet both; P,S meet02; Q,R meet13. At least three
remaining sources meet each position. Indeed at most six sources
belong to the two classes missing that position, and at most two
supporting sources have just been used. Thus two distinct remaining
sources fill02,13.

If F is the supported pair, use target {01,03,12,23}. The same
four peripheral assignments fill01,10,23,32, and two remaining
sources fill03,12. Their class incidences are A,B on both, P,R
on03, and Q,S on12. The same count proves the allocation.

Thus four peripheral classes always give an opposite assembly.

## 3. Exactly three peripheral classes occur {.unnumbered}

Normalize p,q,r>0 and s=0. Since p+q+r≤9, we have a+b≥2.
Two actual sources from A,B can therefore fill either pair E or F
in its forward direction.

### 3.1 An opposite source contains edge 23 {.unnumbered}

Among the varieties high on T, those containing23 are exactly

    W_E={01,02,13,23}, W_F={01,03,12,23}.

Suppose W_F occurs; the other case is symmetric in E,F. Reserve
that source at32. Each of the two other opposite varieties meets E,
because W_F is the unique high variety whose entire T-intersection
is F. If the other two can match the two edges of E, put them at
20,31 and use target W_E.

Otherwise both have exactly the same singleton intersection with
E. As their high patterns are distinct, they are the two adjacent
edge pairs joining that singleton to the two different edges of F.
They therefore match the two edges of F. Put them in the reverse
directions30,21, and use target W_F instead.

In either case the three opposite sources fill the reverse directions
of E or F and the corner32. The adjacent sources P:01, Q:10,
R:23, together with two A,B sources on the forward pair, complete
the target. All eight sources are distinct.

### 3.2 No opposite source contains edge 23 {.unnumbered}

The high varieties avoiding23 are the following five:

| Variety | Underlying edges | Meets03? | Meets13? |
| --- | --- | --- | --- |
| 01|23 | 02,03,12,13 | yes | yes |
| 14|23 | 12,13,24,34 | no | yes |
| 04|23 | 02,03,24,34 | yes | no |
| 01|34 | 03,04,13,14 | yes | yes |
| 01|24 | 02,04,12,14 | no | no |

Among three distinct rows, at least one meets03, at least one
meets13, and at least two meet their union. Thus two distinct
opposite sources fill30,31 on target T'=01|34.

Put P at41 and Q at40. Four forward positions remain:

    03,04,13,14.

The A and R sources contain this whole rectangle. Moreover
a+r≥2, since the complementary three counts b,p,q total at most
nine. Put two A,R sources at04,14. Of the seven adjacent sources
still unused, at least five can fill03 and at least five can fill13:
only Q misses03 and only P misses13, and at most three sources
supporting either position have already been used. Equivalently,
the two neighbour counts are11−q−3 and11−p−3, each at least five.
Choose distinct sources for03,13.

This uses two opposite and six adjacent sources and assembles T'.

All support cases are covered, proving the lemma. The only finite
table is the five high varieties avoiding one specified diagonal;
it is immediate from the six possible two-edge intersections with T.



# Argument 63: Two opposite cubes and thirteen adjacent cubes in the two-star family {#arg-63}

**Theorem.** Let thirteen adjacent sources, each class occurring at
most three times, belong to

    C(01), C(02), C(03), C(04), C(034), C(024), C(023).

Together with any two opposite sources, which may have the same
variety, they contain a five-colour assembly.

Put A=C(01). Every other listed class contains the directed corner01.
If at most two A sources occur, at least eleven adjacent sources
share01, and the common-corner eleven-source lemma applies. Hence
it suffices to prove the following stronger special statement:

> Three A sources, ten capped adjacent sources containing01, and
> any two opposite sources contain an opposite-target assembly.

Write Q={2,3,4} and name the six common-corner classes

    P_i=C(0i), D_i=C({0}∪(Q\{i})), for i∈Q.

The ten-source common-corner pool will be called B. Its class cap is
three. All constructions below use only tricoloured corners, so its
repeated colours are irrelevant.

## 1. An opposite source omits colour0 {.unnumbered}

Use that source's own target, whose parts are {1,i} and {j,k},
where {i,j,k}=Q. Two A copies fill1j,1k. The other six target
positions form J, and the B intersections with J are:

| Class | Positions in J |
| --- | --- |
| P_i | ij,ik |
| P_j | j1,ji |
| P_k | k1,ki |
| D_i | j1,ji,k1,ki |
| D_j | ij,k1 |
| D_k | ik,j1 |

The five two-position patterns are the edges of the path

    ji — j1 — ik — ij — k1 — ki.

The four-position pattern D_i consists of the first two and last
two positions of this path.

The ten B sources have matching rank at least five on J. To prove
this, suppose a Konig cover has at most four vertices. Four corner
vertices contain at most three of the six patterns: if they contain
D_i they are exactly its four positions and contain only the two
end path edges besides it; otherwise four vertices of a path contain
at most three edges. Their class capacity is therefore at most nine.
Three corner vertices contain at most two path edges, hence six
copies, and at most one extra source vertex is allowed. Two corner
vertices contain at most one edge, hence three copies, with at most
two extra source vertices. One or no corner vertices contain no
complete source pattern. Every case fails to cover ten sources.

Match five B sources to five positions of J. The opposite source is
universal on its own target and fills the remaining position. With
the two A copies this is an assembly. The second opposite source
and the third A copy are unnecessary in this case.

## 2. Two different incoming corners at0 {.unnumbered}

Now suppose neither opposite source omits0. If they can supply
incoming corners i0,j0 for distinct i,j∈Q, choose those assignments
on the target with parts01 and ij. Let k be the third colour of Q.

The B sources can fill i1,j1 and one position from {0i,0j}, using
three distinct sources. This is a three-requirement Hall matching:

- i1 is supplied by P_i,D_j,D_k. Its complementary three classes
  have total capacity nine, so at least one of the ten sources
  supplies it. The same holds for j1.
- At least seven sources meet {0i,0j}, since only D_k misses both.
- At least seven sources meet {i1,j1}, since only P_k misses both.
- Each pair consisting of the forward requirement and one incoming
  requirement meets every B source, as does the full three-set.

Thus all Hall inequalities hold. After those three B assignments,
three A copies fill the other three positions of the forward
rectangle. Together with the two opposite assignments i0,j0,
this assembles the target.

## 3. The remaining opposite-source shape {.unnumbered}

Both opposite sources contain0. Each has at least one neighbour of0
in Q, because it has degree two and only one other possible neighbour
is1. If Section 2 does not apply, their neighbour sets in Q are
both the same singleton {i}. Thus both contain the edges01 and0i.
This includes identical opposite varieties.

Let j,k be the other two colours of Q. Consider either target

    T_j={0,j}|{1,i},   T_k={0,k}|{1,i}.

On T_j, put the two opposite sources at10,i0 and two A sources at
0i,1j. The remaining positions are01,j1,ji,ij. Write the B counts as

    a=g(P_i), b=g(P_j), c=g(P_k),
    d=g(D_i), e=g(D_j), f=g(D_k),

with a+b+c+d+e+f=10 and each count at most three. The three
nonuniversal remaining positions have neighbourhood counts

    ji: b+d;  ij: a+e;  j1: b+d+f.

Their matching exists exactly when

    b+d≥1,  a+e≥1,  b+d+f≥2.                   (J)

The pair {ji,j1} gives the last inequality; the other Hall
inequalities follow from the first two and the disjointness of
the class groups supplying ij and ji,j1. After these three sources
are used, any unused B source fills01.

Likewise T_k assembles if

    c+d≥1,  a+f≥1,  c+d+e≥2.                   (K)

Conditions (J) and (K) cannot both fail:

- If b+d=0, then b=d=0. Capacity gives c>0, since a+e+f≤9.
  Also a+f≥4 and c+e≥4, because each complementary pair of
  classes has capacity six. Thus (K) holds.
- If a+e=0, then a=e=0. Now f>0, since b+c+d≤9, and
  c+d≥4, since b+f≤6. Again (K) holds.
- Otherwise b+d≥1 and a+e≥1. Failure of the third condition
  in (J) forces b+d=1 and f=0. The remaining counts satisfy
  a+c+e=9, so a=c=e=3. Every condition in (K) follows.

Hence one of T_j,T_k assembles. Sections 1–3 exhaust every pair
of opposite varieties, proving the stronger special statement and
therefore the two-star-family theorem.




# Argument 64: Three distinct opposite sources with an unsupported common target {#arg-64}

**Lemma.** The opposite sources

    P=O60={13,14,23,24},
    Q=O64={02,04,23,34},
    R=O68={01,03,14,34},

together with eleven adjacent sources of class cap three always
contain a five-colour assembly.

These three varieties have the common high target
T=O61={12,14,23,34}, with edge12 absent from all three sources.
They meet the other three edges in their three different pairs.

The proof uses the already audited global-zero-edge lemma in
[Argument 61](#arg-61) and the common-corner eleven-source lemma in
[Argument 53](#arg-53). Its finite
tables classify only small Hall corner sets against three fixed
targets; no source-inventory search is a premise.

## 1. Reduction to one absent direction on 12 {.unnumbered}

Suppose the pool fails. No underlying edge is absent from the whole
adjacent pool, by the global-zero-edge lemma.

On any opposite target, eleven adjacent sources of class cap three
have matching rank at least four. If their rank is at most four,
all their target intersections lie in four positions. Indeed a
Konig cover of size four with three corner vertices contains at
most nine copies and at most one extra source, hence at most ten.
With two corner vertices it covers at most six copies and two
extras; with at most one corner vertex it cannot cover eleven
sources, each of which meets at least two positions. Thus a rank
at most four cover must consist of four corner vertices alone.

If the adjacent pool supplies both directions of12, its union on T
has at least five positions: those two, and at least one on each of
the other three underlying edges. Its rank on T is therefore at
least five. Match the two12 positions first, using distinct adjacent
sources, and extend that independent position set to a five-position
matching. This is ordinary matching augmentation.

The three remaining positions lie on edges14,23,34. The three
opposite sources fill any three such positions. Every one of these
edges has two opposite neighbours; every pair of edges has all
three neighbours. These are all Hall inequalities for three
positions. Thus T assembles, a contradiction.

Consequently one direction of12 is absent from every adjacent
source. Reverse all directed corners if necessary, so the absent
corner is12. The fourteen possible adjacent outsets are

    234,02,03,124,04,123,12,034,024,023,23,24,34,012.

An outset S denotes the class C(S)=S→Sᶜ.

## 2. The Hall inequalities to be retained {.unnumbered}

Use P,Q,R themselves as candidate targets. On each, its own source
is universal and the other two sources meet one distinct underlying
edge each. Denote those two edges by G_1,G_2 and the other two by F.
For a set Z of target positions, the number of opposite neighbours is

    a(Z)=1+#{i : Z meets G_i}.

Let D(Z) be the adjacent classes, among the fourteen allowed above,
which avoid Z. A Hall obstruction requires

    number of adjacent sources outside D(Z) ≤ k(Z),
    k(Z)=|Z|−1−a(Z).

We may discard an obstruction of either of these kinds:

- k=0 and Z contains both directions of an edge: all adjacent
  sources would avoid that edge, and the global-zero-edge lemma
  applies.
- k≤2 and Z contains both directions of two underlying edges:
  at least nine adjacent sources would avoid both edges. This
  already gives an assembly by the elementary nine-avoider lemma
  in [Argument 9](#arg-9), Section 1.

We may also discard k=0 whenever every class in D(Z) shares a
corner, by the common-corner eleven-source lemma. Finally any row
with 3|D(Z)|+k<11 is impossible by the class cap.

### Why only three small shapes remain {.unnumbered}

All Hall sets of size at least five satisfy their inequalities.
For five positions with all three opposite neighbours, the three-
position complement contains at most three adjacent classes, hence
at most nine cubes: at least two adjacent neighbours remain. If
there are only two opposite neighbours, the complement contains
both directions of the missed G_i edge and at most one further
position; at most two adjacent classes fit there. For six positions,
at most two classes fit in the complement, while at least two
opposite sources meet the set. Sets of seven or eight positions
meet every adjacent source. These bounds suffice in each case.

For sets of at most four positions, the formula for a(Z) leaves
only these undominated possibilities after the two discard rules:

1. Two positions, one on each edge of F, with k=0.
2. Three of the four positions on F, with k=1.
3. One position on each edge of F and both directions of one G_i,
   with k=1.

To check this directly, a three-position k=0 set either contains
a bidirected edge or contains a pair from item 1. A four-position
set meeting only one G_i either contains a triple from item 2 or
has the shape in item 3; if its F positions are a whole edge, the
two-edge discard rule applies. A four-position k=0 set either
contains a bidirected edge or a pair from item 1. The full four-
position F set is discarded by the nine-avoider lemma. Sets with
negative k give no obstruction.

For P the two F edges are13,24; for Q they are02,04. Intersecting
the fourteen allowed cuts with the three listed shapes gives the
following complete reduced tables. All unlisted candidates in
these shapes have at most three avoiding classes, except the
k=0 pair {31,24} for P, whose four avoiders all contain43, and
the k=0 pair {20,04} for Q, whose four avoiders all contain41.
Those two exceptions are discarded by the common-corner lemma.

## 3. The two Hall tables {.unnumbered}

### Target P {.unnumbered}

| Row | Z | k | D(Z), written as outsets |
| --- | --- | ---: | --- |
| a | 31,42 | 0 | 02,124,123,12,024,24,012 |
| a' | 13,24 | 0 | 234,03,04,034,024,24,34 |
| b | 13,42 | 0 | 234,02,03,123,024,023,23,24 |
| c | 13,31,42 | 1 | 02,123,024,24 |
| c' | 13,24,42 | 1 | 234,03,024,24 |
| d | 13,23,32,42 | 1 | 234,123,023,23 |
| d' | 13,14,41,42 | 1 | 02,03,023,23 |

### Target Q {.unnumbered}

| Row | Z | k | D(Z), written as outsets |
| --- | --- | ---: | --- |
| A | 02,40 | 0 | 02,123,12,024,023,23,012 |
| B | 20,40 | 0 | 02,03,04,034,024,023,012 |
| C | 02,04 | 0 | 234,124,123,12,024,23,24,34 |
| D | 02,20,40 | 1 | 02,024,023,012 |
| E | 02,04,40 | 1 | 123,12,024,23 |

Let sigma interchange colours1,2, interchange3,4, and reverse
every directed corner. It preserves P, exchanges Q,R, and preserves
the absent direction12. On outsets its action is

    sigma(S) = complement of (1 2)(3 4)(S).

Therefore the R table is exactly the sigma-image of the Q table.
For completeness its avoiding sets are:

| R row | k | Avoiding outsets |
| --- | ---: | --- |
| sigma(A) | 0 | 234,03,034,023,23,24,34 |
| sigma(B) | 0 | 234,124,123,12,23,24,34 |
| sigma(C) | 0 | 02,03,04,034,024,023,24,012 |
| sigma(D) | 1 | 234,23,24,34 |
| sigma(E) | 1 | 03,034,023,24 |

## 4. The three targets cannot all fail {.unnumbered}

Choose one obstruction row for each target and write their avoiding
sets as D_P,D_Q,D_R and their bounds as k_P,k_Q,k_R. Put

    I=D_P∩D_Q∩D_R,  k=k_P+k_Q+k_R.

Every adjacent source outside I lies outside at least one of the
three avoiding sets. Hence at most k sources lie outside I, and
the class cap gives

    11 ≤ 3|I|+k.                                      (1)

The displayed sets have the intersection bound

    |I| ≤ 4−k.                                       (2)

Here is the complete small intersection check. For each Q row and
R row, the entry (m_0,m_1) gives the maximum intersection size with
a P row of k_P=0 and of k_P=1, respectively. It is obtained simply
by intersecting the displayed finite sets; no multiplicities occur
in this table.

| Q row / R row | sigma(A) | sigma(B) | sigma(C) | sigma(D) | sigma(E) |
| --- | --- | --- | --- | --- | --- |
| A | (2,2) | (2,2) | (3,2) | (1,1) | (1,1) |
| B | (2,2) | (0,0) | (4,3) | (0,0) | (2,2) |
| C | (3,2) | (4,3) | (2,2) | (3,2) | (1,1) |
| D | (1,1) | (0,0) | (3,2) | (0,0) | (1,1) |
| E | (1,1) | (2,2) | (1,1) | (1,1) | (0,0) |

Rows A,B,C and their images have bound zero; D,E and their images
have bound one. The table proves (2). If k≥1, equations (1),(2)
give 11≤12−2k≤10, a contradiction.

Thus all three selected rows have k=0. To hold eleven cubes, I
must have four classes. The only entries permitting this are
(B,sigma(C)) and (C,sigma(B)). In the first case the P row must
be a' or b, and the intersections are respectively

    {03,04,034,024},   {02,03,024,023}.

Every class in either set contains01. The second case is the
sigma-image: its four-class intersections are

    {124,123,12,24},   {234,123,23,24},

and all these classes contain20. In either case all eleven adjacent
sources share a corner and already assemble by the common-corner
lemma. This is the final contradiction.

Consequently P,Q,R cannot all fail after the preceding solved cases
have been removed. The unsupported triad therefore assembles.




# Argument 65: Three distinct opposite cubes and eleven adjacent cubes {#arg-65}

**Theorem.** Three pairwise distinct opposite-repeat five-colour
cubes, together with eleven adjacent-repeat cubes whose
tricoloured-corner class counts are at most three, contain eight
cubes assembling a five-colour 2×2×2 cube with monochromatic faces.

The conclusion permits an adjacent target. In particular the
common-corner lemma used below proves an assembly by repeated-colour
arguments; the stronger computational observation that an opposite
target always exists is not needed or asserted as proved here.

## 1. The geometric inputs {.unnumbered}

An adjacent class is a directed cut C(S)=S→Sᶜ on five colours,
where |S| is two or three. An opposite variety is a four-cycle and
supplies both directions of each of its four underlying edges.

On an opposite target, every adjacent class has two or four corners,
on distinct underlying edges. At most two adjacent classes have
their entire intersection inside two specified positions, and at
most three inside three specified positions. These are the elementary
cut facts in [Argument 1](#arg-1),
Section 1.

Call an opposite source high on a target if it meets at least two
underlying target edges. The following two four-cycle facts were
proved independently of the numerical four-opposite theorem in
[Argument 9](#arg-9), Section 3:

1. Any three distinct opposite varieties have a common high target.
2. On a fixed target, a specified two-edge intersection determines
   its distinct high source variety uniquely.

The first follows by using the line of a neighbouring pair, or by
closing a four-cycle through two edges of a missing three-edge path
when all three pairs are nonneighbours. The explicit four-row
classification is given in that note.

Three additional elementary lemmas are used:

- [Argument 61](#arg-61): if all eleven adjacent sources avoid one
  underlying edge, the pool has an opposite assembly;
- [Argument 62](#arg-62): if the adjacent sources are all confined
  to one directed half of a common high target, the pool assembles;
- [Argument 53](#arg-53): eleven
  capped adjacent sources containing one common directed corner
  already assemble, without using any opposite source.

## 2. The adjacent matching dichotomy {.unnumbered}

On any fixed opposite target T, the eleven adjacent sources either
have matching rank at least five, or all their intersections are
contained in four directed positions.

Indeed, a Konig cover of size at most four with three corner
vertices covers at most nine source copies through those corners,
and at most one other source through its source vertex. A cover
with two corner vertices covers at most six copies and two extras.
With at most one corner vertex, every adjacent source requires a
source vertex, since it meets at least two positions. None covers
eleven sources. Thus any cover of size at most four must consist
solely of four corner vertices.

Suppose, for contradiction, that the whole pool fails. The first
additional lemma lets us assume every underlying edge occurs in
the adjacent pool. Also nine adjacent sources cannot all avoid
two underlying edges: meeting edges have only two reverse avoiding
classes, while disjoint edges have four avoiding classes in two
orientations; nine copies then yield an assembly with at most one
opposite source. This nine-avoider argument is written in
[Argument 9](#arg-9), Section 1.

Consequently any pair of underlying edges has at least three
adjacent-source neighbours.

## 3. A fully supported common high target {.unnumbered}

Choose a common high target T, and first suppose the union of the
three opposite varieties covers every edge of T.

### Adjacent matching rank at least five {.unnumbered}

The four underlying target edges can be matched to four distinct
adjacent sources. Every single edge has a neighbour; every pair
has at least three neighbours; and every three-edge set meets all
eleven sources, because each adjacent class uses at least two of
the four target edges. Hall proves the matching.

Choose a compatible directed position on each edge. Extend this
four-position independent set to five matched positions by an
augmenting path. The five positions still cover all four underlying
edges. Their three-position complement therefore uses three
distinct underlying edges.

The three opposite sources fill this complement. A single edge
has a neighbour by full support. Any two edges have at least two
neighbours: only the unique high variety whose intersection is
the complementary pair can avoid them. Any three edges meet all
three high sources. These are all Hall inequalities needed for
three positions on distinct edges.

### Adjacent matching rank at most four {.unnumbered}

All adjacent target intersections lie in four positions H, by
Section 2. Since every underlying edge is covered, H contains
exactly one direction on each of T's four edges. Regard H as an
orientation of the square.

A directed cycle is impossible: a cut confined to its directions
would have to place all four vertices on the same side. That is
incompatible with a 2|3 cut of five colours.

If the square orientation has two sources and two sinks, it is
alternating, and H is one directed half of an opposite target.
The rectangle-family lemma applies.

Every other acyclic orientation of a square has a unique source a
and a unique sink b. A cut whose target intersection is confined
to H has its outset downward closed along this orientation. Its
restriction to the four target vertices is nonempty and proper,
again because a whole side cannot contain four vertices. Such a
set contains a and excludes b. Thus every adjacent source contains
the same directed corner ab, whether or not ab is an edge of T.
The common-corner eleven-source lemma applies.

Both matching ranks therefore contradict failure. This closes the
fully supported common-target case.

## 4. The unsupported common target {.unnumbered}

If the common target is not fully supported, its three distinct
high source patterns are the three two-edge subsets of three
target edges. Indeed there cannot be only two supported edges,
by uniqueness of a two-edge high pattern. None of the sources is
T, so each meets exactly two edges, and distinctness gives all
three pairs. The supported edges form a three-edge path.

There is only one unmarked geometric form. A convenient
representative is

    O60={13,14,23,24},
    O64={02,04,23,34},
    O68={01,03,14,34},

on common target O61={12,14,23,34}, whose edge12 is unsupported.
Every two-edge pattern determines its variety, so this normalization
leaves no hidden choice of opposite source.

The complete closure is [Argument 64](#arg-64). If the adjacent
pool supplies both directions of12, extend those two positions
to a five-corner adjacent matching; the opposite sources fill any
three positions on the other three edges. Otherwise normalize the
absent direction to12. The three source varieties themselves are
used as candidate targets. Their possible Hall obstructions reduce
to seven rows on one target and five rows on each of the other two,
which are symmetric.

Each row requires all but at most k=0 or1 adjacent sources to lie
in a stated avoiding set. Three selected rows have common avoiding
set I satisfying |I|≤4−(k_1+k_2+k_3). The class cap makes every
choice with a positive k impossible for eleven sources. The only
zero-k intersections large enough are four-class common-corner
families, already solved by the common-corner lemma. The complete
small set-intersection certificate is displayed in that note.

Thus the unsupported target case also assembles, completing the
proof for three distinct opposite sources.




# Argument 66: Three opposite cubes and eleven capped adjacent cubes {#arg-66}

## Theorem {.unnumbered}

Take three opposite-repeat five-colour cubes and eleven adjacent-repeat
five-colour cubes. If no adjacent tricoloured-corner class occurs more
than three times, eight of these fourteen cubes assemble a five-colour
2×2×2 cube with monochromatic faces.

There is no restriction on the multiplicities of the three opposite
varieties. The conclusion permits either an adjacent-repeat or an
opposite-repeat target. All sources are physical cubes, and an assembly
uses eight distinct sources with compatible proper rotations.

## Proof by the opposite multiplicities {.unnumbered}

There are three possibilities.

1. **Three distinct varieties.** Apply the theorem in
   [Argument 65](#arg-65).
   Its proof uses Hall's theorem on a common high target. A fully
   supported target reduces to a rank-five matching, a directed
   rectangle, or a common-corner family. The unique unsupported triad
   is handled by displayed small Hall-obstruction tables and their
   set intersections. Each of these component proofs has been audited.

2. **One doubled variety and one different variety.** Apply
   [Argument 60](#arg-60).
   Hall's theorem on the doubled variety reduces failure to a
   five-position cover. A missing bidirected edge is impossible;
   otherwise the three missing directions form a path. Its monotone,
   one-change, and alternating orientations are all solved in the
   accompanying hand proofs, retaining both possible single varieties
   when a symmetry does not preserve the marked source.

3. **Three identical varieties.** The earlier elementary classification
   in [Argument 22](#arg-22) says that a fourteen-cube failure containing
   three identical opposite cubes has adjacent class sizes 5,3,3.
   This contradicts the present adjacent class cap of three.

These cases exhaust the three opposite sources. No inventory search
is a premise of the argument.



