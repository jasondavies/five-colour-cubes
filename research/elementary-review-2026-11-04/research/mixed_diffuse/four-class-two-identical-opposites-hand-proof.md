# Four adjacent copies and two identical opposite sources

**Status: elementary proof.** The one-opposite branch is proved in
`four-class-one-opposite-hand-proof.md`.

**Theorem.** A fourteen-pool containing four copies of an adjacent
tricolour class and exactly two opposite sources, both of the same
variety, is soluble.

We use the notation and proved constructions of the five-class note.
Its theorem already excludes adjacent class counts at least five, so
all such counts may be assumed at most four. Normalize the chosen
four-copy class to A=C(01), and write O for the opposite variety.

The following bounds hold in a failure:

* At most two adjacent sources are disjoint from A, by
  4A+three-disjoint+O.
* A class of size at least three has disjoint-adjacent mass at most
  two, by 3B+three-disjoint+two-O.
* Two adjacent classes sharing four corners have combined count≤7.

## 1. Hall reduction

Reserve a same-repeat A pair, leaving two A for tricoloured positions.
The ten outside sources must have matching rank at most three on A.
A vertex cover with no corner vertices would leave at least seven
disjoint sources. A cover with one corner and two source vertices must
use both source vertices for the opposite copies, leaving at least
six adjacent sources in one singleton-intersection class. Both are
impossible.

For a cover with two corners and one exceptional source, use the
thirteen-cube corollary in the five-class note: if an adjacent source
is exceptional, retain the two O and seven covered adjacent sources;
if an O is exceptional, retain the other O and all eight adjacent
sources. Therefore all remaining cases have a three-corner cover H.

In particular O∩A has size two. If O met A in four corners, neither
of the possible covers could contain even one of its copies, and
the pool would already solve. The two corners form either a row pair
or a diagonal pair in A's two-by-three array.

## 2. Row pair, with H itself a row: H={02,03,04}

Normalize O to opposite04∣23, omitting1, so O∩A={02,03}.
Its two copies fill20,30 in the reverse half of rectangle01∣23.
Thus helpers matching21,31 complete the rectangle with four A.

If no such helper pair exists, one of21,31 is absent: otherwise only
one helper could meet either position, leaving at least seven helpers
in C(04), the unique eligible class missing both. Interchanging2 and3,
suppose21 is absent. The eight helpers then belong to

    X=C(03), Y=C(04), Z=C(034), W=C(34).

If W occurs, use one W at40 in rectangle01∣34 and one O at30.
The seven remaining helpers match31,41: each sees at least one, and
neither position can be absent without forcing seven copies of X or Y.
Thus W is absent.

Let x,y,z be the remaining class counts, with x+y+z=8. Four X solve:
reserve a same-repeat pair, use two X at31,32, A at04, O at34, and
two Y/Z sources at01,02. Four Y solve using two remaining Y at01,41,
two A at02,03 and the two O at42,43. Thus x,y≤3.

If z=4, then x+y=4 and both x,y are positive. Reserve a same-repeat
Z pair; two Z fill01,32, while X fills31, Y fills41, O fills42 and
A fills02. Hence z≤3. The counts are therefore a permutation of3,3,2.

### Repeated-colour contradiction

Each class has a loop: two copies with the same repeated colour solve.
Here are the tricoloured assignments after reserving the indicated pair:

| Target and reserved pair | Six tricoloured positions |
|---|---|
| X, two X | Z:31,32; A:04; O:34; Y:01,02 |
| Y, two Y | Z:01,41; A:02,03; O:42,43 |
| Z, two Z | X:31,32; Y:41,42; A:02; one further X/Y:01 |

The last extra source exists because x+y≥5.

The three classes also conflict pairwise whenever they use the same
repeated colour:

* **X,Y:** reserve one of each for an X target's bicoloured corners.
  Use Z at31,32, A at04, O at34, and two remaining X/Y/Z at01,02.
* **X,Z:** their only possible common repeat is4. They supply an A
  target's poles0,1. Four A fill12,13,14,02; a remaining X fills04
  and a Y fills03.
* **Y,Z:** their only possible common repeat is3. They again supply
  an A target's poles0,1. Four A fill12,13,14,04; a remaining Y
  fills03 and an X fills02.

Consequently all eight X/Y/Z copies would have different repeated
colours, impossible with five colours. This closes the row cover.

## 3. Row pair, with H={02,03,12}

Again O is opposite04∣23. The helper classes are

    B=C(234), D=C(134), R=C(04), E=C(034), F=C(024),
    Z23=C(23), Z24=C(24), Z34=C(34).

Only D has an A corner outside O∩A. If d≤1, discard that source and
apply the thirteen-cube corollary with the other seven helpers. Thus
d≥2. Also R cannot occur four times: after reserving an R pair, use
the other two R at01,41, two A at02,03 and the two O at42,43. Hence r≤3.

Try rectangle01∣34, using O at30 and three helpers at31,40,41.
The helper pools are

    31: B,E,Z23,Z34;
    40: B,D,Z24,Z34;
    41: B,R,E,F,Z24,Z34.

All pair and triple Hall bounds hold: the first two pools have union
8−r−f≥2 since d≥2; the first and third have union8−d≥4; the last
two have union8−z23≥6. The40 pool is nonempty, and the41 pool has at
least8−d−z23≥2 sources. Thus failure forces31 to be absent.

Only D,R,F,Z24 remain. In rectangle01∣24, use O at20 and ask the
helpers to fill21,40,41. The pools are F+Z24, D+Z24 and R+F+Z24.
Their pair unions have sizes at least5,4 and8 respectively. The last
two pools are nonempty; the first is nonempty as well, since otherwise
d+r=8 contradicts d≤4,r≤3. Hall gives the required three-matching.

## 4. Row pair, with H={02,03,14}

Write

    R=C(04), D=C(123), E=C(034), F=C(024),

and let z count the other four, disjoint-from-A classes. Only D meets
A outside O∩A, so d≥2 by the thirteen-cube corollary. As above r≤3.

D is disjoint from R,E,F. If d≥3, the disjoint-mass bound gives
r+e+f≤2. Since d+r+e+f+z=8 and z≤2, this forces d=4,z=2.
But every disjoint-from-A source meets D in a corner of O. A meets
D at14, outside O. Therefore two O, one such source and one A match
four D corners; after reserving a D pair, the two remaining D complete
the target. Hence d=2 and r+e+f=6−z≥4.

If z>0 and a disjoint source sees40, use it there. Another helper
sees21 or31: either another disjoint source exists, or e+f>0, since
z=1,e=f=0 would give r=5. A further R/E/F source fills41. Together
with O at20 or30 these helpers complete rectangle01∣24 or01∣34.

If no disjoint source sees40, all z sources are C(23). They can fill
21,31 with each other or with E/F; again e+f>0 when z=1. The two O
fill20,30 and rectangle01∣23 solves. Thus z=0.

If E and F both occur, they fill31,21 with the two O at20,30, solving
the same rectangle. Otherwise interchange2 and3 so F is absent.
Now r+e=6. Assemble opposite04∣12: four R/E sources fill their common
positions01,02,41,42; A fills14; D fills10; the two O fill20,24.

Sections 2–4 prove the theorem whenever O has a row-pair intersection
with the chosen four-copy class. We may use this conclusion for any
other four-copy class as well.

## 5. Diagonal pair, with H={02,03,12}

Now O is opposite02∣13, omitting4. The helper classes are the same
as in Section 3. Every class among D=C(134), R=C(04), F=C(024) has
either four O corners or a row-pair O intersection. By Section 1 or
Sections 2–4, its count is at most three.

Also E=C(034) has count at most three. If it had four, reserve a
same-repeat pair. O fills01,32 and A fills02. Every other eligible
helper class has a corner in {31,41,42}; use one there and the two
remaining E at the other two positions. There is such a helper since
the total helper count is eight.

Let d,r,e,f≤3 be these counts and z≤2 the disjoint-from-A mass.
Try rectangle01∣34, with O at30 and helpers at31,40,41. As in Section 3,
their pair unions have sizes8−r−f≥2,8−d≥5,8−z23≥6. The41 pool
cannot be empty. Thus failure forces either31 or40 to be absent.

* If31 is absent, the only helpers are D,R,F,Z24. If Z24 occurs,
  rectangle01∣24 solves with O at21 and helpers at20,40,41: use
  Z24 at20, and the remaining helpers match40,41. Indeed d+z24≥2,
  since d=0,z24=1 would force r+f=7>6. If Z24 is absent, then
  d+r+f=8, so each count is at least two. Assemble O itself using
  A:03,12; D:10,32; F:21,23; R:01; O:30.
* If40 is absent, the only helpers are R,E,F,Z23. If Z23 occurs,
  rectangle01∣23 solves with the two O at21,30 and helpers at20,31:
  Z23 supplies20, and another Z23 or E supplies31. Such another
  source exists, since e=0,z23=1 would force r+f=7>6. If Z23 is
  absent, then r+e+f=8, with each count at least two. Assemble O
  using A:03,12; O:10,30; F:21,23; E:32; another helper:01.

This closes the first diagonal shape.

## 6. Diagonal pair, with H={02,03,14}

Now O is opposite04∣12, omitting3. Let

    R=C(04), D=C(123), E=C(034), F=C(024).

Each has either four O corners or a row-pair intersection, so all
four counts are at most three by the established cases.

Try O itself. Two A fill02,14. For its six other positions

    Y={01,10,20,24,41,42},

the helper intersections are

| Helper | Intersection with Y |
|---|---|
| R,E | 01,41,42 |
| D | 10,20,24 |
| F | 01,41 |
| C(234),C(24) | 20,41 |
| C(23) | 20,24 |
| C(34) | 41,42 |

If the helpers match four Y positions, the two O fill the rest.
Suppose their rank is at most three. Every helper has at least two
Y positions. A cover with two Y vertices and one source vertex would
put at least seven helpers into one identical two-position pattern;
the table and the bounds f≤3,z≤2 make that impossible. Therefore all
helper intersections lie in three Y positions.

Unless those positions are {01,41,42}, the table permits at most five
helpers: at most three from D or F and at most two disjoint-from-A
sources. Consequently all helpers belong to R,E,F,Z34=C(34).

Write z for the Z34 count. We have r+e+f+z=8, with r,e,f≤3,z≤2.
If f>0, assemble opposite12∣34, omitting0. Use A at13,14, F at23,
O at24, and fill31,32,41,42 from R,E,Z34. This four-matching exists:
E and Z34 see all four positions, R sees41,42, and

    e+z≥8−r−f≥2,     r+e+z≥5.

If f=0, necessarily r=e=3,z=2. Assemble rectangle01∣34 using four A
forward, O at41, E at31, and the two Z34 at30,40.

All cases are soluble, proving the theorem.

## Consequence and remaining gap

All mixed four-class branches with at least two opposite sources are
elementary-closed, whether the opposite varieties are distinct or
identical. The companion one-opposite proof extends the conclusion to
every mixed diffuse fourteen-cube failure: all adjacent class counts
are at most three.
