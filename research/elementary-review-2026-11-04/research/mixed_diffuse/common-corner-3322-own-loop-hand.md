# A common-corner 3,3,2,2 core with a looped triple

**Status: elementary proof.** The three support cases below are the
three possible forms of two absent classes in a six-class common-corner
family. No computer classification of failures is used.

**Lemma.** Suppose four distinct adjacent tricolour classes have a
common directed corner. They occur with multiplicities `3,3,2,2`.
If either of the triple classes admits an own-orientation loop in the
full pool, the full pool is soluble.

An own loop may use any extra sources in the full pool. All other
matchings in this proof use just the ten sources in the stated core.

## 1. Notation and the three possible supports

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

## 2. Three classes of one kind and one of the other

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

## 3. Two matched pairs of classes

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

## 4. Two unmatched absent classes

The remaining support is `P3,P4,D2,D4`.

### Two intrinsic loops and four edges

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

### Neither intrinsic-loop class can be a triple

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

### The remaining two triples

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
