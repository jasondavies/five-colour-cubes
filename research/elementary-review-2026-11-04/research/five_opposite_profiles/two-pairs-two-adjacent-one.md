# Two opposite pairs, one opposite single, and two adjacent classes

**Theorem.** Let P,Q,R be distinct opposite varieties, and let A,B be
distinct adjacent tricoloured-corner classes. The eight sources

    2P + 2Q + R + 2A + B

assemble an opposite target.

This strengthens the fourteen-source conclusion for opposite profile
2,2,1. The neighbouring case was already proved in
`../opposite_small_lemma/five-opposites-neighbouring-pairs.md`.
The proof below handles P,Q sharing only one undirected edge. It uses
four grid forms, followed by four explicit exceptional matchings.
No exhaustive inventory list is a premise.

## 1. A replacement observation

If 2P+2Q+R+3A assembles an opposite target, then 2P+2Q+R+2A+B does
as well, for any B. Indeed the three A positions use three distinct
underlying target edges, whereas B meets at least two target edges.
Choose a common edge. Replace the A assigned there by B, interchanging
the two directions of that edge in the assignment first if needed.
The source in the reverse position is opposite, because A never
contains both directions of one edge, so the interchange preserves
its compatibility. The other two A assignments are unaffected.

We may consequently assume that the temporary pool with 3A fails.
Normalize A=C(01)={0,1}→{2,3,4}. Its six corners form the grid

    02 03 04
    12 13 14.

Each opposite variety meets the grid in either a two-column rectangle
or a pair of positions in different columns. These fifteen patterns
are all distinct.

## 2. Reduction to four grid forms

No two-column rectangle can have opposite matching rank four. If it
did, four opposite sources would fill the reverse rectangle, and the
remaining opposite source plus 3A would fill the forward rectangle.
Every opposite source meets that forward rectangle on some edge.

Submodularity of matching rank therefore bounds the full grid rank by
four. The matching form of Hall's theorem gives a grid set H with

    |H| + #{opposite source copies whose pattern is not in H} ≤ 4.

There is no such H of size at most two: at most one opposite variety
fits in two positions, allowing at most two copies. Both doubled
patterns lie in H. Neither is a rectangle, because H would then equal
that rectangle, and five capped sources supported there match all
four corners. (The one-, two-, and three-position Hall inequalities
follow from the respective capacities of the complementary three,
two, and one grid positions.)

Thus each doubled variety has a two-position grid pattern. If the
patterns overlap, their union uses two columns: a three-position set
on three columns has its three two-position patterns forming a line
of mutually neighbouring opposite varieties, whereas P,Q share only
one edge. Row exchange and column permutation give the single form

    P∩A={02,03}, Q∩A={12,03}.

If the patterns are disjoint, their union cannot be a two-column
rectangle, since the two copies of each variety would match all four
positions. The union therefore has column sizes 2,1,1, and R's pattern
also lies in it. There is one form when the two singleton positions
are on the same row, and two when they are on different rows. These
are the three rows of the table in Section 4.

For reference, the variety labels used below are only abbreviations:

| Variety | Undirected edges |
|---|---|
| O61 | 12,14,23,34 |
| O63 | 03,04,23,24 |
| O64 | 02,04,23,34 |
| O65 | 02,03,24,34 |
| O68 | 01,03,14,34 |
| O70 | 01,04,12,24 |
| O71 | 01,02,14,24 |
| O73 | 01,03,12,23 |

Each undirected edge supplies both directed corner positions.

## 3. The overlapping form

Here P=O65 and Q=O73. If R contains edge13, the five opposite sources
match the four corners on columns2,3, contrary to our reduction. The
only opposite varieties avoiding all three edges13,14,04 are P,Q:
those three forbidden edges form a four-vertex path, whose two
avoiding four-cycles omit one or the other internal vertex. As R is
distinct from P,Q, it therefore contains04 or14.

If R contains04, use target O63. Assign 2A to03,04 and R to40. The
remaining corners are

    E={23,32,24,42,30}.

The two P copies see30,24,42, while the two Q copies see30,23,32.
They fill any four corners of E. The only adjacent class avoiding E
is A: the bidirected edges23,24 force2,3,4 together, and avoiding30
fixes the orientation. Since B≠A, B supplies the fifth corner.

If R contains14, use target O68. Assign 2A to03,14 and R to41. The
remaining set is

    E={01,10,30,34,43}.

Again 2P+2Q fill any four positions of E. The only avoiding adjacent
classes are A and C(012): avoiding bidirected01 and34 fixes the two
pairs on opposite sides, while avoiding30 fixes their orientation;
colour2 may join either side. Thus this construction works unless
B=C(012). In that exception use target O61 with the explicit matching

| Sources | Assigned corners |
|---|---|
| 2P | 34,43 |
| 2Q | 21,32 |
| R | 41 |
| 2A | 12,14 |
| B=C(012) | 23 |

This only requires that R contain14, so it handles every overlapping
exception at once.

## 4. The three disjoint forms

The three normal forms are as follows. The target T contains the four
underlying edges a,b,d,e; the corners a,b belong to A, d=P∩Q, and e
is absent from P,Q. Every permitted R contains e and at least one of
the underlying edges a,b.

| P,Q | P∩A; Q∩A | T | a,b | d,e | Possible R |
|---|---|---|---|---|---|
| O65,O70 | 02,03;12,04 | O63 | 03,04 | 24,23 | O63,O64,O73 |
| O61,O65 | 12,14;02,03 | O68 | 14,03 | 34,01 | O68,O71,O73 |
| O71,O73 | 02,14;12,03 | O68 | 14,03 | 01,34 | O61,O65,O68 |

There are two completion mechanisms.

**Edge-e completion.** If B meets e, assign B to that corner and R
to its reverse. Assign 2A to a,b. The two P copies fill the reverse
of a and one direction of d; the two Q copies fill the reverse of b
and the other direction of d. This fills T.

**Second completion.** If R contains the underlying edge a, use target
P. Assign 2Q to both directions of d, R to the reverse of a, and 2A
to the two P∩A corners. Three positions remain. If B meets any of
them, B fills that position and the two universal P copies fill the
other two. When R contains b, use the symmetric construction on Q.

Let E_a and E_b combine the three positions in the second completion
with both directions of e. A B source meeting the relevant E enables
one of the two completions. The following table gives these sets and
all their avoiding classes other than A.

| P,Q | E_a | Extra avoider | E_b | Extra avoider |
|---|---|---|---|---|
| O65,O70 | 20,34,43,23,32 | none | 01,10,21,23,32 | C(014) |
| O61,O65 | 21,23,32,01,10 | C(014) | 20,24,42,01,10 | C(013) |
| O71,O73 | 20,24,42,34,43 | none | 21,23,32,34,43 | none |

The avoiding-class assertions follow by keeping each bidirected edge
on one side of a cut and using the remaining directed edge to fix the
orientation. If the two bidirected edges meet, their three vertices
stay together and only A avoids. If they are disjoint, the fifth
vertex can join either pair, giving exactly the two listed cuts.

In the first row, R=O63 orO73 contains a, so E_a completes. The only
possible exception is R=O64, B=C(014).

In the second row, R=O68 contains both a and b. The extra avoiding
classes for E_a and E_b differ, so no B≠A avoids both sets. The
possible exceptions are R=O71, B=C(014), and R=O73, B=C(013).

The third row has no exception. Its permitted R always contains a or
b, and the corresponding rescue set is met by every B≠A.

## 5. Explicit matchings for the three remaining exceptions

In every row A=C(01). Each displayed target corner occurs exactly once.

| P,Q,R | B | Target | 2P | 2Q | R | 2A | B corner |
|---|---|---|---|---|---|---|---|
| O65,O70,O64 | C(014) | O65 | 34,30 | 42,24 | 20 | 02,03 | 43 |
| O61,O65,O71 | C(014) | O65 | 43,34 | 30,24 | 20 | 02,03 | 42 |
| O61,O65,O73 | C(013) | O61 | 41,23 | 43,34 | 21 | 12,14 | 32 |

All source compatibilities can be read directly from the edge table
and the directed cuts. This completes the disjoint forms, the
nonneighbouring case, and the theorem.

## Consequence for the current fourteen-cube target

For five opposite sources of profile2,2,1 and nine capped adjacent
sources, either nine distinct adjacent classes occur and the
nine-class theorem applies, or some A occurs twice. Since not all
nine adjacent sources can belong to A, choose an occupied B≠A.
The eight-source theorem above then gives an assembly.

This proof is stronger than the rescue-count adaptation in
`two-doubles-fourteen.md`, which is retained as the shortest route to
the current target.
