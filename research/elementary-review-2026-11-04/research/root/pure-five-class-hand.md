# Five copies in one class in an all-adjacent fourteen-pool

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

## 1. A useful eight-cube construction

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

## 2. Hall cover reduction

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

## 3. Column and diagonal covers

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

## 4. Row cover: numerical reduction

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

## 5. Row cover: repeated-colour contradiction

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

