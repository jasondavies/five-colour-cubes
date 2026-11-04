# Hand elimination of three-anchor cover orbits 30 and 51

Notation is as in `elementary_refinements.md`: an adjacent class is named by
its outgoing set; X=O(0;12|34) is available three times. Adjacent counts are
at most five, shared-four pairs have combined count at most seven, and each
other opposite type has count at most three. Corner labels `ab` mean a→b.

## Mask30: four adjacent classes

The classes and counts are

    A=02 (a), B=123 (b), C=023 (c), D=23 (d),
    a+b+c+d=11,
    a+c≤7, b+d≤7, c+d≤7.

No other opposite type occurs.

### A class of count at least four gives a target

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

### The remaining counts are 3,3,3,2

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

## Mask51: a three-leaf star and two opposite types

The classes and counts are

    A=01 (a), B=03 (b), C=13 (c), D=013 (d),
    Y=O(2;03|14) (p), Z=O(4;01|23) (q),
    a+b+c+d+p+q=11,
    a+d≤7, b+d≤7, c+d≤7.

The permutation (1 3)(2 4) fixes X,C,D and exchanges A with B and Y with Z.

### Opposite targets reduce the possibilities

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

### Completion after a repeated pair in a large adjacent class

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

### Collections with all adjacent counts at most three

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
