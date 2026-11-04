# Four adjacent copies and four diffuse opposite sources

**Status: elementary proof, using only explicit small corner tables.**
This note proves the g≥4, O≥4 part of the remaining diffuse branch.

**Theorem.** A fourteen-pool containing at least four copies of one adjacent
tricolour class and at least four opposite-repeat sources, with no opposite
variety occurring more than twice, is soluble.

Indeed a stronger local assertion suffices: after the four opposite
sources fail to match four corners of that adjacent class, any two
additional adjacent sources complete a solution, unless one already
completes the adjacent target directly.

Use the notation of `five-class-mixed-hand-proof.md`: `ab` is a directed
corner, C(S)=S→Sᶜ, and an opposite target is the bidirected K₂,₂ between
two disjoint pairs. Normalize the four-copy class to A=C(01).

## 1. Reduction to seven tiny configurations

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

## 2. Two matching observations

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

## 3. Three corners in one row

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

### 3.1. Two S and two T

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

### 3.2. One R, one S, two T

In T, the residual intersections of R and S are the disjoint triples
{24,30,42} and {20,34,43}. By the second matching observation the only
exceptions are two helpers from the same singleton row of the T column:
two C(02), C(03), C(034), or C(024).

The symmetry interchanging2 and3 exchanges the first two and the last
two cases. For two C(02), assemble R using A at03,04, the helpers at23,24,
R at40, S at32, and T at30,42. For two C(034), use A at03,04, the helpers
at32,42, R at40, S at23, and T at24,30.

This closes the row shape.

## 4. Two corners in a column

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

## 5. Three columns, split between the rows

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

### 5.1. Two U and two V

For either target the other variety's residual triple is {01,10,41}.
By the first matching observation, the U construction can fail only
if both helpers are C(034), and the V construction can fail only if
both are C(024). They cannot both fail.

### 5.2. Two T and two V

The common residual triple is {20,24,42}. The T construction can fail
only for two C(034) or two C(024); the V construction can fail only
for two C(23). Again one construction works.

### 5.3. One T, one U, two V

In V, the residual intersections of T and U are the disjoint triples
{20,24,42} and {01,10,41}. Every helper sees at least two positions of
V outside A, so the second matching observation always applies.

### 5.4. Two T, one U, one V

In T, the residual intersections of U and V are the disjoint triples
{30,34,43} and {20,24,42}. The second observation works unless the
helpers are both C(034) or both C(024). By interchanging2 and3 it is
enough to treat two C(034). Assemble V using

    A:02,14; helpers:01,41; T:20,24; U:10; V:42.

This closes the last shape and proves the theorem.

## Scope

The argument uses a two-table geometric case split, not an exhaustive
search of cube inventories or repeated-colour refinements. The case
split is complete because it is exactly the classification of three
positions of a two-by-three array and four edges of the resulting
triangle/path with edge multiplicity at most two.

The cases with one, two or three total opposite sources and maximum
adjacent multiplicity four remain outside this theorem. With at least
four opposite sources, every remaining diffuse failure has all adjacent
class counts at most three. This conclusion is elementary and does not
depend on the separate finite eight-cube lemma.
