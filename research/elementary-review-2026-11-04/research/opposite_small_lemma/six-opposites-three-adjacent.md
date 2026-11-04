# Six diffuse opposite cubes and three cubes in one adjacent class

**Status: elementary proof.** The argument uses Hall's theorem, the
submodularity of matching rank, and the neighbouring-pairs lemma in
`two-neighbouring-opposite-pairs.md`. It does not use exhaustive search.

**Lemma.** Six opposite-repeat sources, with no opposite variety occurring
more than twice, together with three sources from one adjacent tricolour
class, always assemble an opposite target. Thus nine sources suffice.

The repeated colours of the three adjacent sources are irrelevant.

## 1. The two-by-three grid

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

## 2. A Hall cover with at most four positions

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

### Three positions

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

### Four positions in two columns

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

## 3. Four positions in all three columns

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

## Consequences and an independent check

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
