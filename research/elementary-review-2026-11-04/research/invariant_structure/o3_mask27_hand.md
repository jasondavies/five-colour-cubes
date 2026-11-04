# Hand elimination of three-anchor cover orbit27

Use three copies of X=O(0;12|34). The allowed adjacent classes and counts are

    A=01 (a), B=123 (b), C=023 (c), D=23 (d),

and the other opposite types are Y=O(2;03|14) [67] and Z=O(4;01|23) [72],
with counts p,q. Thus

    a+b+c+d+p+q=11,
    a,b,c,d≤5,  p,q≤3,  b+d≤7,  c+d≤7.

The opposite-triangle extension lemmas give p+q≤3 in a failure. If both
counts are at least two, the 3X+2Y+2Z core plus any extra cube solves. If one
count is three and the other positive, the 3,3,1 core plus a cube different
from its two large types solves; such an extra cube exists by the caps and
the fourteen-cube total. Consequently at least eight adjacent cubes remain.

## 1. A four-position Hall reduction

Consider target T=O(3;04|12) [71]. Corners41,42 are supplied only by X among
the allowed groups, so reserve two X for them. The third X can fill14 or24.
Every adjacent cube also fits14 or24, and at least eight adjacent cubes
exist. Therefore it suffices to match the four positions

    Q={01,02,10,20}

to distinct nonanchor cubes. Once this is done, an unused adjacent cube
and the third X fill14,24. The intersections with Q are:

| Source | Available positions |
|---|---|
|A|02|
|B|10,20|
|C|01|
|D|20|
|Y|01,10|
|Z|02,20|

Every three-position subset has at least six neighbours (it excludes at
most one adjacent class of count≤5), and all four have eleven neighbours.
Among the six pairs, four are automatically safe: their neighbour counts
are a+c+p+q=11-b-d≥4; a+b+p+q=11-c-d≥4;
b+c+d+p+q=11-a≥6; and a+b+d+q=11-c-p≥3.
The other two pairs have neighbour counts b+c+p and b+d+p+q.

Thus if T cannot be assembled, at least one of the following conditions holds:

1. c=p=0 (position01 missing);
2. a=q=0 (position02 missing);
3. b=p=0 (position10 missing);
4. b=d=q=0 (position20 missing);
5. b=c=0,p=1 (01 and10 have only one common source);
6. b=1,d=p=q=0 (10 and20 have only one common source).

For the last two cases, we have assumed all individual positions supported;
any other pair deficiency is already included among1–4. This is a direct
four-position Hall calculation, with no multiplicity enumeration.

## 2. All cases with a>0 are soluble

A useful second target is Z itself. Reserve two X for13,31. Its other six
positions split into L={02,03,12} and R={20,21,30}. A fits all of L; B fits20,30;
C fits21; D fits all of R; Y fits none; and Z fits all six. Hall's condition
for these two blocks is satisfied if

    a+q≥3,
    b+d+q≥2,
    c+d+q≥1,
    a+b+d+q≥5,
    a+c+d+q≥4.                         (*)

The two additional full-block inequalities are automatic: R has
11-a-p≥3 neighbours and all six positions have11-p≥8. The five displayed
inequalities are the strongest requirements for L, {20,30}, {21},
L∪{20,30}, and L∪{21}, respectively; all smaller subsets follow.

Assume a>0. Condition2 of the previous section is impossible.

* In condition1, c=p=0. The pair cap b+d≤7 gives a+q≥4. The total gives
  b+d+q=11-a≥6 and a+d+q=11-b≥6. Also d+q≥1, since otherwise a+b=11 would
  contradict the class caps. All of(*) hold, so Z is assembled.
* In condition3, b=p=0. Now c+d≤7 gives a+q≥4, while a+d+q=11-c≥6 and
  c+d+q=11-a≥6. Thus(*) hold unless d+q≤1. In that exception a+c≥10;
  the caps and total force a=c=5,d+q=1. A same-repeat pair among the five
  A cubes fills an A target's bichromatic positions; the remaining three
  A fill02,03,12, one C fills04, and two X fill13,14.
* In condition4, b=d=q=0 and a+c+p=11. If p≤2, one of a,c is five. Five A
  with any C solve as just described. Five C with any A similarly solve:
  reserve a same-repeat C pair; use C:01,21,34, A:04, X:24,31. If p=3,
  then a,c≥3, and target Y is assembled by Y:10,40,43; X:13,31;
  C:01,34; A:04.
* In condition5, b=c=0,p=1 and a+d+q=10. Since a,d≤5, both a+q and d+q
  are at least five, so every inequality(*) holds.
* In condition6, the total forces a=c=5. The five-A construction above
  applies.

Hence every collection in this cover with a>0 is soluble.

## 3. The cases with a=0

Suppose first that q>0. Conditions2 and4 are impossible. Condition1 would
give b+d+q=11, contradicting b+d≤7 and q≤3. Condition3 gives the same
contradiction with c+d. Condition5 would give d+q=10, contradicting d≤5,
q≤3. Condition6 requires q=0. Therefore the four-position matching succeeds
and T is assembled. A failure must have q=0.

Now a=q=0 and b+c+d+p=11. The pair caps imply

    b+p≥4,  c+p≥4.

If p=2, then b,c≥2. Assemble target Y by Y:40,43; X:13,31; C:01,04;
B:10; and any further B,C,D cube at34. If p=3, then b,c≥1; use
Y:40,43,01; X:13,31; C:04; B:10; and a further adjacent cube at34.
The extra cube exists because at least eight adjacent cubes are available.

It remains p≤1, so b+c+d≥10 and b,c≥3. Some class has count at least four.
Reserve two same-repeat copies in that class for its bichromatic positions;
the following table supplies its six tricoloured positions:

| Case/target | Tricoloured placements |
|---|---|
|b=4, B|B:10,20; D:30; C:34; X:14,24|
|b=5, B|B:10,20,30; C:34; X:14,24|
|c=4, C|C:01,04; D:21; B:34; X:24,31|
|c=5, C|C:01,04,21; B:34; X:24,31|
|d≥4, D|D:21,34; B:20,30; X:24,31|

When b=4 or c=4, the other two counts sum at least six and neither exceeds
five, so d≥1 as required. In the final row at least two D remain after the
reserved pair, and b≥3 supplies the two B. All cases therefore solve.

This closes cover orbit27 using only the established caps, two elementary
Hall calculations on four and six positions, and explicit corner assignments.
