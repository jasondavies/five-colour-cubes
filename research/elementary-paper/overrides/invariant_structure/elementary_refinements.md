# Elementary refinements of the three observed fourteen-cube configurations

Research note, 3 November 2026. These are elementary proofs **conditional on a
specified coarse configuration**. They do not establish that the three
configurations exhaust all failing collections. All variety/class indices below
refer to `../root/cut_model.py`.

## 1. Notation

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

## 2. A concentrated-opposite extension

Write $O=O(0;12\mid34)$, $A=C(01)$, and $B=C(124)$.

### A useful extension lemma

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

## 3. The pure-adjacent family: nine derangements

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

## 4. The opposite-three family: a unique refinement

Take three O=O(2;03|14), five A=δ⁺(014), three B=δ⁺(24), and three
C=δ⁺(124). The permitted repeated colours are respectively

    A: 0,1,4;   B: 0,1,3;   C: 1,2,4.

**Proposition.** The collection fails exactly when all A repeat0, all B
repeat3, and C contains one copy of each repeated colour1,2,4.

If two C cubes have the same repeated colour, use them for their target's
two bichromatic corners; three B cubes fill20,23,40 and three O cubes fill
10,13,43. Therefore every repeated colour in C has count at most one, hence
each has count exactly one.

If A uses repeated1, an A_1 cube and C_1 cube fill β(1,2),β(1,3), leaving four
A cubes for the private tricoloured corners02,03,12,42 and two O for13,43.
If B uses repeated1, B_1 and C_1 fill the same bichromatic corners, and four
A plus two O fill the tricoloured ones. Thus neither A nor B uses repeated1.
The identical argument with C_4 excludes repeated4 from A. Hence all five A
repeat0. If B uses repeated0, A_0 and B_0 give the two A_0 bichromatic corners,
and the same six tricoloured placements complete a target. Consequently all
three B repeat3.

For the converse, available bichromatic pairs allow only these five adjacent
varieties: A_0,B_3,C_1,C_2,C_4, or their reversed cuts. The tricoloured union
omits14,24,30,32, excluding the reversed cuts. A_0 has four private
tricoloured plus two private bichromatic corners, but only five A cubes.
B_3 has two private tricoloured plus two private bichromatic corners, but
only three B cubes. Each C_r has two private bichromatic corners but only
one copy. The bidirectional graph has a unique four-cycle, corresponding
to O; that target has four private corners01,04,31,34 and only three O cubes.

The colour-permutation/global-reversal stabilizer is trivial. A is the
unique class of weight five, and reversal changes the size of its outgoing
side, so a stabilizer cannot use reversal. The repeated colour2 of O is
fixed; A's complementary pair23 then fixes3; B's outgoing pair24 fixes4;
C's outgoing triple124 fixes1; finally0 is fixed. There are thus 120·2=240
coarse labelled configurations, each with exactly one refinement.

## 5. Opposite-triangle extension lemmas

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

## 6. Three-anchor Hall covers of size at most three

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

## 7. A general identity that may help further work

If f(a,b) is the total multiplicity of tricoloured corner ab, and
d_a=Σ_{S:a∈S}g_S, then

    f(a,b)−f(b,a)=d_a−d_b.

Opposite varieties contribute symmetrically. For one cut, the difference
is precisely 1_S(a)−1_S(b); summing proves the identity. Consequently the
directed frequency imbalance has zero circulation around every triangle.
No elementary proof deriving W=36 from this identity has been found.
