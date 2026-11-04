# Hand elimination of three-anchor cover orbits 23, 53, and 102

Use X=O(0;12|34) three times. All adjacent-class counts are at most five;
each other opposite variety has count at most three. A shared-four adjacent
pair has total at most seven. The missing-pair bound says that the total
number of cubes omitting a fixed bichromatic colour pair is at most seven.

## Mask23

The allowed groups are A=01 (a), B=124 (b), Y=O(2;03|14) (p), and
Z=O(4;01|23) (q), with a+b+p+q=11.

The opposite-triangle extension lemmas show p+q≤3 in a failure. Indeed,
p,q≥2 gives the 3,2,2 core, while one count3 and the other positive gives
the 3,3,1 core plus an additional cube different from its two large types.
Such an additional cube must exist since every opposite count is at most3.

Therefore a+b≥8. If a=5, any Y or Z meets an A-private corner; two same-repeat
A fill the bichromatic positions, three A fill three private corners, Y/Z
fills the fourth, and two X fill13,14. There is necessarily a Y or Z because
a+b≤10. The same argument handles b=5. Thus a=b=4 and p+q=3. If p≥2,
make a B target: reserve two same-repeat B for its bichromatic positions;
the two remaining B and two Y fill its four private corners10,20,40,43
(Y fits10,40,43); two X fill13,23. If q≥2, the symmetric A target works,
because Z fits three of the four A-private corners02,03,04,12. One of p,q
is at least two, completing the proof.

## Mask53

The adjacent classes are A=03 and B=124, with counts a,b. The allowed
opposite types and counts are

    U=O(1;03|24) [64], u;
    Y=O(2;03|14) [67], y;
    Z=O(4;01|23) [72], z;
    V=O(4;02|13) [73], v;
    W=O(4;03|12) [74], w.

All eleven nonanchor cubes lie in these groups. The adjacent varieties with
poles03 and the opposite varieties U,Y,W omit the bichromatic pair03.
Consequently

    a+b+u+y+w≤7,

and hence z+v≥4. Since z,v≤3, both are positive.

If z,v≥2, use three X, two Z, and two V. These seven cubes can fill any seven
corners of target W. To see this, W's corners split into three pairs/blocks:

    P={01,10}, Q={02,20}, R={13,31,23,32}.

Two V cover P, two Z cover Q, and three X cover three corners of R. This
handles a hole in R. If the hole lies in P, the spare V fills23 or32 and X
fills the other three R corners. If it lies in Q, the spare Z fills13 or31
and X fills the other three R corners. Any eighth cube shares a corner
with W, so it fills one of the permissible holes and completes W.

The remaining count pattern is {z,v}={3,1}. The colour permutation (1 2)
exchanges Z,V and U,Y while preserving X,A,B,W, so take z=3,v=1. Three X
fill23,31,32 of W; three Z fill13,02,20; one V fills one of01,10. Any extra
cube having01 or10 fills the other. Every cube of A,B,Y,W has at least one
of those corners. If none of those groups occurs, the remaining seven
nonanchor cubes must all be U, contradicting u≤3. Thus W is constructible.

## Mask102

The adjacent classes are

    A=13 (a), B=024 (b), C=24 (c), D=013 (d),

and the allowed opposite types are

    E=O(0;13|24) [61], e;
    U=O(1;03|24) [64], u;
    V=O(2;04|13) [68], v;
    Y=O(3;01|24) [69], y;
    Z=O(4;02|13) [73], z.

Their counts total eleven. Set F=a+d, R=b+c, K=u+v, L=y+z. The shared-four
bound gives F,R≤7 and the individual opposite bound gives K,L≤6. This
orbit does not require the missing-pair bound.

### Hall's condition for E

Every allowed source intersects target E in at least four corners; E itself
intersects it in all eight. Thus a set of at least five target corners has
all fourteen cubes as neighbours. A set of at most three corners meeting
X has its three anchor cubes as neighbours. A set of four corners meeting
X also has a nonanchor neighbour: otherwise all eleven nonanchor cubes
would have exactly the same four-corner intersection with E. The only
groups with identical four-corner intersections are A,D (total F≤7) and
B,C (total R≤7); each of U,V,Y,Z has its own distinct intersection and
count≤3. Hence eleven such cubes cannot exist.

It remains to inspect subsets of

    Q=E\X={12,21,34,43}.

The intersections of the nonanchor groups with Q are:

| Group | Available corners of Q |
|---|---|
|F=A∪D|12,34|
|R=B∪C|21,43|
|K=U∪V|34,43|
|L=Y∪Z|12,21|
|E|all four|

Any pair in Q has at least four neighbouring cubes: a same-row pair omits
only F or R (each at most seven of eleven), a same-column pair omits only
K or L (each at most six), and a diagonal pair meets every group. Any set
of three or four corners meets every group. Consequently the only possible
Hall failure for E is an entirely unsupported single corner of Q:

    F+L+e=0, F+K+e=0, R+L+e=0, or R+K+e=0.

Global arc reversal exchanges F,R; the colour permutation (1 3)(2 4)
exchanges K,L while preserving F,R. We may therefore assume

    F=L=e=0.

Thus only B,C,U,V remain, with b+c+u+v=11. Since b+c≤7, u+v≥4. Since u,v≤3,
both are positive.

### Three explicit completions

If u,v≥2, take any B or C cube T, which exists because b+c≥5. Make target
O(1;02|34) [63] with X:24,32,42; U:04,40; V:03,30; T:23.

If u=3,v=1, then b+c=7 and b,c≤5 give b,c≥2. Make the same target63 with
X:24,32,42; U:23,40,04; V:30; B:03.

If u=1,v=3, again b+c=7 gives b,c≥2. Make target O(2;01|34) [66] with
X:41,31,13; U:04; V:14,30,03; C:40.

These cases exhaust u+v≥4 with u,v≤3, proving that mask102 has no failure.

All three orbit proofs use only the stated caps and explicit assignments or
the elementary four-position Hall argument above. No multiplicity search is
needed.
