# Nine distinct adjacent classes: an explicit Hall-table proof

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

## 1. Six possible cores

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

## 2. The Hall calculation used by every table row

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
in `six-doubled-classes-hand.md`. For nine distinct sources, therefore,
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

## 3. Possible helper sets when a target fails

In the following tables, a normal row means all four helpers must lie
in the displayed D-set. A row with k=1 instead means at most one helper
lies outside D. For k=1 the displayed D has three members, so all three
must be present. The corner set S is supplied to make each obstruction
checkable directly from the cut definition.

### Core 1: {01, 02, 03, 04, 12}

| Target | Corner set S | D(S) | k |
| --- | --- | --- | ---: |
| 14∣23 | {31,34} | {134, 124, 024, 14, 014, 24, 012} | 0 |
| 14∣23 | {42,43} | {234, 123, 13, 023, 23, 013, 012} | 0 |
| 02∣14 | {40} | {123, 034, 13, 024, 023, 23, 014, 013, 012} | 0 |
| 02∣14 | {10,21,24,40} | {034, 014, 013} | 1 |
| 02∣13 | {30} | {124, 034, 024, 14, 023, 014, 24, 013, 012} | 0 |
| 02∣13 | {10,21,23,30} | {034, 014, 013} | 1 |

The first target forces H into one of its two seven-element sets, neither of which contains `034`. Thus the k=1 alternatives for the other two targets are impossible, since both require `034`. The intersection of a first-target set with both remaining k=0 sets has only three members: respectively `{024,014,012}` or `{023,013,012}`. Four distinct helpers cannot lie there.

### Core 2: {01, 02, 03, 12, 13}

| Target | Corner set S | D(S) | k |
| --- | --- | --- | ---: |
| 02∣13 | {10,21,23,30} | {04, 034, 014, 013} | 0 |
| 02∣13 | {01,21,30,32} | {124, 14, 014, 012} | 0 |
| 03∣12 | {01,20,23,31} | {134, 14, 014, 013} | 0 |
| 03∣12 | {10,20,31,32} | {04, 024, 014, 012} | 0 |

Every D-set for the first target meets every D-set for the second in at most 2 classes. Hence four distinct helpers cannot make both targets fail.

### Core 3: {01, 02, 03, 12, 14}

| Target | Corner set S | D(S) | k |
| --- | --- | --- | ---: |
| 02∣14 | {10,21,24,40} | {04, 034, 014, 013} | 0 |
| 02∣14 | {40,42} | {123, 13, 024, 023, 23, 013, 012} | 0 |
| 03∣12 | {01,20,23,31} | {134, 13, 014, 013} | 0 |
| 03∣12 | {31,32} | {124, 04, 123, 024, 014, 24, 012} | 0 |

Every D-set for the first target meets every D-set for the second in at most 3 classes. Hence four distinct helpers cannot make both targets fail.

### Core 4: {01, 02, 03, 12, 34}

| Target | Corner set S | D(S) | k |
| --- | --- | --- | ---: |
| 01∣24 | {12,14,20} | {04, 034, 024, 023} | 0 |
| 01∣24 | {40,41} | {123, 13, 023, 23, 014, 013, 012} | 0 |
| 02∣13 | {03,10,12,23} | {234, 034, 023, 23} | 0 |
| 02∣13 | {10,21,23} | {04, 034, 014, 013} | 0 |
| 02∣13 | {01,21,30,32} | {124, 14, 014, 012} | 0 |

Every D-set for the first target meets every D-set for the second in at most 2 classes. Hence four distinct helpers cannot make both targets fail.

### Core 5: {01, 02, 03, 14, 24}

| Target | Corner set S | D(S) | k |
| --- | --- | --- | ---: |
| 03∣24 | {32,34} | {234, 124, 04, 12, 024, 014, 012} | 0 |
| 03∣24 | {20,40,43} | {034, 13, 023, 013, 012} | 0 |
| 02∣14 | {10,21,24,40} | {04, 034, 014, 013} | 0 |
| 02∣14 | {10,42} | {234, 024, 023, 23, 013, 012} | 0 |

Every D-set for the first target meets every D-set for the second in at most 3 classes. Hence four distinct helpers cannot make both targets fail.

### Core 6: {01, 02, 13, 24, 34}

| Target | Corner set S | D(S) | k |
| --- | --- | --- | ---: |
| 01∣23 | {02,13} | {234, 134, 123, 024, 023, 23} | 0 |
| 01∣23 | {03,13,20,21} | {134, 03, 034, 013} | 0 |
| 01∣23 | {02,12,30,31} | {124, 12, 024, 012} | 0 |
| 02∣13 | {01,21,23} | {134, 123, 14, 014, 013} | 0 |
| 02∣13 | {10,30,32} | {04, 024, 023, 014, 012} | 0 |

Every D-set for the first target meets every D-set for the second in at most 2 classes. Hence four distinct helpers cannot make both targets fail.

## 4. Completeness details for the small Hall tables

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

## Consequence for fourteen cubes

An opposite-unsoluble all-adjacent pool has at most eight occupied
tricoloured-corner classes. If a fourteen-pool had every class count
at most two, at least six of those classes would have count two.
The corollary in `six-doubled-classes-hand.md` would then solve it.
Thus a pure fourteen-cube failure has a class of size at least three.

Together with the separate four- and five-class proofs and the older
six-class bound, every pure fourteen-cube failure has maximum class
count exactly three. This does not yet prove that its support is a
butterfly, or that its class-size profile is 3,3,3,3,1,1.

## Sharpness

The bound nine is sharp even when adjacent targets are allowed. An explicit
eight-cube counterexample, with a direct Hall proof, is given in
`eight-distinct-class-counterexample.md`.
