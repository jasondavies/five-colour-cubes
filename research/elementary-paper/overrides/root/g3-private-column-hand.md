# Private columns force a butterfly

**Theorem.** Let a failing pool consist of fourteen adjacent-repeat cubes.
Suppose no class of multiplicity three is completable in its own
orientation after two copies have been reserved. Then the pool is
contained in a butterfly support family. Consequently the earlier
butterfly classification gives the class-size profile `3,3,3,3,1,1`.

This is a hand argument, using the already proved facts that a pure
fourteen-failure has maximum class size three, has at most five repeated
classes, and that, under the present hypothesis, each triple class has
exactly two private corners in a column. The stronger private-column lemma in
`../pure_supported/private-diagonal-unconditional-hand.md` proves this
without assuming that the other triples lack own completions.

Here `ab` means the directed corner a→b, and C(S) is the directed cut
S→Sᶜ on the five colours. A private corner of a class belongs to no
other occupied class. A butterfly support family has no supported
opposite target; the elementary classification of such families is
in `../support_families/elementary-support-family-proofs.md`.

## 1. Normalize one triple class

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

## 2. Three classes cannot be triples

### H has at most two copies

A covers four of H's six corners, leaving only {23,24} as possible
private corners. If H were a triple, both would be private. Avoiding
{02,12,23,24} leaves only A,B,Z34 besides H. Four classes with cap
three contain at most twelve cubes. Thus h≤2.

### B has at most two copies

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

### Z34 has at most two copies

Suppose A and Z34 are triples, and use target 01∣34. They supply the
two universal halves. Each L/R helper meets both halves and would
complete the target with any second helper. The remaining helpers split
into forward-only classes P,Q,H and reverse-only classes B,Z23,Z24.
Both kinds occurring again complete the target. If all helpers are
forward-only, every corner of Z34 is private. If all are reverse-only,
every corner of A is private. Thus z34≤2.

## 3. A second triple must exist

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

## 4. A triple P or Q forces butterfly support

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

## 5. Any triple L/R class forces butterfly support

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

## 6. The remaining zero classes cannot be triples

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

## 7. Conclusion

Section 3 forces a second triple. Sections 2 and 6 exclude H,B and all
Z classes as that triple. It must therefore be P,Q or an L/R class,
and Sections 4 and 5 force a butterfly support family.

The earlier elementary butterfly classification now gives exactly four
triple classes and two singleton classes. In particular, for this entire
branch,

    A_stat = 4 binom(3,2)=12,    B_stat=0,    3A_stat−4B_stat=36.

This closes the all-private pure branch. It does not settle a pool with
an own-orientation looped triple; that is a separate remaining branch.
