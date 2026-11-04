# Three distinct opposite sources with an unsupported common target

4 November 2026

**Status: elementary Hall-table proof; full independent root audit
passed.** The separate root geometric checker also verified all
small corner-set conditions and displayed table entries.

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
`global-zero-edge.md` and the common-corner eleven-source lemma in
`../three_opposite_double/common-corner-eleven-hand.md`. Its finite
tables classify only small Hall corner sets against three fixed
targets; no source-inventory search is a premise.

## 1. Reduction to one absent direction on 12

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

## 2. The Hall inequalities to be retained

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
  in `../four_opposite_root/common-high-targets.md`, Section 1.

We may also discard k=0 whenever every class in D(Z) shares a
corner, by the common-corner eleven-source lemma. Finally any row
with 3|D(Z)|+k<11 is impossible by the class cap.

### Why only three small shapes remain

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

## 3. The two Hall tables

### Target P

| Row | Z | k | D(Z), written as outsets |
| --- | --- | ---: | --- |
| a | 31,42 | 0 | 02,124,123,12,024,24,012 |
| a' | 13,24 | 0 | 234,03,04,034,024,24,34 |
| b | 13,42 | 0 | 234,02,03,123,024,023,23,24 |
| c | 13,31,42 | 1 | 02,123,024,24 |
| c' | 13,24,42 | 1 | 234,03,024,24 |
| d | 13,23,32,42 | 1 | 234,123,023,23 |
| d' | 13,14,41,42 | 1 | 02,03,023,23 |

### Target Q

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

## 4. The three targets cannot all fail

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

## Proof status and computation

The tables were found and checked with `triad_hall_explore.py`.
Their mathematical completeness is supplied by the three-shape
Hall classification in Section 2, and the entire set-intersection
certificate is displayed in Section 4. The proof uses no enumeration
of adjacent count vectors or of repeated-colour refinements.
