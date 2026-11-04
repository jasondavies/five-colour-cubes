# Four adjacent copies and one opposite source

**Status: elementary proof.** This closes the last mixed four-class
branch. The row-triple subcase is proved in the companion note
`one-opposite-row-cover-hand-proof.md`.

**Theorem.** Every fourteen-pool containing exactly one opposite-repeat
source and at least four copies from one adjacent tricolour class is
soluble.

Use directed corners `ab`, adjacent classes C(S)=S→Sᶜ, and opposite
varieties given by bidirected complete bipartite graphs on two pairs.
The mixed five-class theorem already handles a class of size at least
five. In a putative failure, therefore, every adjacent class has count
at most four. Normalize a four-copy class to A=C(01).

We use the established shared-four bound and two eight-cube constructions:

    4B + three adjacent sources disjoint from B + O solve;
    3B + four adjacent sources disjoint from B + O solve.

Thus a four-copy class has disjoint-adjacent mass at most two, and a
three-copy class has disjoint-adjacent mass at most three.

## 1. A two-corner transfer lemma

Suppose the nine adjacent sources outside A meet A only in a two-corner
set P. Then four A together with those helpers and O solve.

If O∩A⊆P, retain any eight helpers and use the thirteen-cube corollary
of `five-class-mixed-hand-proof.md`.

Otherwise O has an A corner outside P. Apply the explicit two-corner
cover constructions in Sections 3–5 of
`research/root/pure-five-class-hand.md`. Their numerical assumptions
hold here: our class bound four is stronger than the bound five there,
the shared-four bound is unchanged, and the disjoint mass is at most
two. All of those constructions use at most four A except the
two conflicts between A and a singleton-intersection class in the
final row-cover case. In either such conflict one A has been reserved
for a bicoloured position, and four A were used at the four corners
outside P. Here use O at one of those corners and the three remaining
A at the other three. Every other displayed construction transfers
without change. This proves the lemma.

This use of the pure five-class proof concerns its displayed post-cover
constructions. The initial five-A matching-rank reduction is not needed.

## 2. Hall reduction and the rectangle exclusion

Reserve a same-repeat A pair for its bicoloured positions, leaving two
A. The ten outside sources must have matching rank at most three on
A's six tricoloured positions. König's theorem gives a cover with at
most three source/corner vertices.

A cover without a corner vertex leaves at least seven adjacent sources
disjoint from A, impossible. A cover with one corner vertex must use
an exceptional source vertex for O. Even if another adjacent source is
exceptional, at least eight adjacent sources remain covered by that
single corner. At most two are disjoint, so at least six belong to
the unique singleton-intersection class, again impossible.

For a cover with two corners and one exceptional source, use Section 1
if O is exceptional. If an adjacent source is exceptional, the other
eight helpers and O lie in the pair O∩A, and the thirteen-cube corollary
applies directly.

Consequently every remaining case has a three-corner cover H for all
outside sources. O∩A has exactly two corners, in different columns.
In particular, **a four-copy class meeting O in four corners already
solves**. We may use this rectangle exclusion for any other class.

Up to the stabilizer of A, there are five covered configurations:
three with O∩A a row pair, and two with O∩A a diagonal pair.

## 3. Row pair, with H={02,03,04}

Normalize O to opposite04|23, omitting1. This is precisely the case
proved in `one-opposite-row-cover-hand-proof.md`.

That proof first solves whenever a helper is disjoint from A. With
no disjoint helpers it reduces one opposite target to a six-position
path matching problem. Hall sets of size at least three are controlled
by the shared-four bound. The remaining singleton and pair conditions
reduce to three support families, each of which forces three looped,
pairwise conflicting classes with counts3,3,3. The resulting demand
for nine different repeated colours is impossible.

## 4. Row pair, with H={02,03,12}

Again O is opposite04|23. The nine eligible helpers belong to

    B=C(234), D=C(134), R=C(04), E=C(034), F=C(024),
    Z23=C(23), Z24=C(24), Z34=C(34).

Only D meets A outside O∩A. If d≤1, discard that source and apply
the thirteen-cube corollary to eight helpers contained in O∩A.
Hence d≥2. Also r≤3 by the rectangle exclusion: R has four O corners.

Try rectangle01|34, with O at30 and helpers at31,40,41. Their pools are

    31: B,E,Z23,Z34;
    40: B,D,Z24,Z34;
    41: B,R,E,F,Z24,Z34.

The pair unions have sizes9−r−f≥2,9−d≥5,9−z23≥7. The40 pool is
nonempty since d≥2, and the41 pool has at least9−d−z23≥3 sources.
Thus Hall can fail only when31 is absent.

Only D,R,F,Z24 then remain. Use rectangle01|24, with O at20 and
helpers at21,40,41. These pools are F+Z24, D+Z24 and R+F+Z24.
Their pair unions have sizes at least6,5 and9. The last two pools are
nonempty. The first is also nonempty, since otherwise d+r=9 would
contradict d≤4,r≤3. The required three-matching exists.

## 5. Row pair, with H={02,03,14}

O is still opposite04|23. The nonzero-intersection helper classes are

    R=C(04), D=C(123), E=C(034), F=C(024).

Write z≤2 for the other helpers, which are disjoint from A. Only D
meets A outside O∩A, so d≥2 as above. Both R and D have four O
corners, so r,d≤3 by the rectangle exclusion.

D is disjoint from R,E,F. If d=3, its disjoint mass would be
r+e+f=9−d−z≥4, contrary to the three-copy disjoint-mass bound.
Therefore d=2, and r+e+f+z=7.

One D and O fill20,30 in rectangle01|23. If two other helpers match
21,31, the rectangle solves with four A. At least e+f+z=7−r≥4
helpers meet one of21,31. Hence absence of such a two-matching forces
one position to be absent. Interchanging2 and3, assume21 is absent.
Then F,B,Z23,Z24 are absent, and the disjoint helpers are all Z34.
Thus r+e+z=7.

If z>0, use Z34 at40 and O at30 in rectangle01|34. Two remaining
R/E/Z34 helpers match31,41: after reserving that Z34, the31 pool
has e+z−1≥3 sources, and all six remaining helpers see31 or41.

Thus z=0. The bounds r≤3,e≤4 and r+e=7 force r=3,e=4. Reserve a
same-repeat E pair. The two other E fill31,32. R sees all four common
corners01,02,41,42, and O sees02,42, so the three R and O fill those
four positions. This assembles E.

Sections 3–5 prove that a four-copy class with a row-pair O intersection
solves. We may now use that conclusion for any helper class as well.

## 6. Diagonal pair, with H={02,03,12}

Now O is opposite02|13, omitting4. The eligible helper classes are
the same as in Section 4. D=C(134) and F=C(024) each have four O
corners; R=C(04) has a row-pair O intersection. Their counts d,r,f
are therefore at most three.

E=C(034) also has count at most three. If e=4, reserve a same-repeat
E pair, put O at32 and A at02, and let two other helpers fill two
different positions in {01,31,41,42}; the two remaining E fill the
other two. Such a helper pair exists. Each of the five other helpers
meets this set. Those with only one position are D at42, Z23 at31,
and Z24 at41; each such class has count at most three (indeed the
disjoint classes have total at most two). Every other eligible helper
sees at least two positions. Five helpers therefore cannot all be
confined to one common position.

Now d,r,e,f≤3 and z≤2. Try rectangle01|34 with O at30 and helpers
at31,40,41. Its pair unions have sizes9−r−f≥3,9−d≥6,9−z23≥7,
and the41 pool is nonempty. Failure forces31 or40 to be absent.

If31 is absent, only D,R,F,Z24 remain. When Z24 occurs, rectangle01|24
solves with O at21, Z24 at20 and two helpers at40,41. After reserving
the Z24, the40 pool has d+z24−1≥2 sources and the41 pool has at
least five. When Z24 is absent, d+r+f=9 forces d=r=f=3. Assemble O
using A:03,12; D:10,32; F:21,23; R:01; O:30.

If40 is absent, only R,E,F,Z23 remain. If Z23 occurs, both E and F
occur, because otherwise the total helper count is at most3+3+2=8.
Use rectangle01|23 with O:30, Z23:20, E:31, F:21 and four A forward.
Thus only r=e=f=3, with no disjoint helpers, remains.

### The remaining repeated-colour triangle

The three classes R,E,F all have loops. After reserving a same-repeat
pair from the named target class, use:

| Target | Six tricoloured positions |
|---|---|
| R | A:02,03; E:41,42; F:01,43 |
| E | remaining E:31; O:32; A:02; R:41,42; F:01 |
| F | remaining F:21; O:23; A:03; R:41,43; E:01 |

They also conflict pairwise. R and E can share only repeat3, and R and
F only repeat2. In either case their poles supply0,1 for an A target.
Four A fill04,12,13,14; a remaining E fills02 and a remaining F fills03.

If E and F share a repeat, reserve one of each for an E target's poles
1,2. The two remaining E fill31,32, A fills02, two R fill41,42, and
O fills01. Thus E and F also conflict.

Three pairwise disjoint repeated-colour sets of size three would be
required, a contradiction.

## 7. Diagonal pair, with H={02,03,14}

Here O is opposite04|12, omitting3. Let

    R=C(04), D=C(123), E=C(034), F=C(024).

R,D,E each have four O corners, and F has a row-pair O intersection.
Consequently r,d,e,f≤3. The disjoint-from-A count is z≤2, and
r+d+e+f+z=9.

Try O itself. Two A fill02,14, and the other six positions split into

    C={01,41,42},       L={10,20,24}.

R and E see all C; F sees01,41. There are at least four R/E/F sources,
and r+e≥1, since otherwise the total count is at most3+3+2=8.
Therefore three R/E/F sources match all C.

D sees all L. The disjoint helpers have L intersections

    B=C(234), Z24: {20};   Z23: {20,24};   Z34: empty.

If two sources from D and the disjoint classes match two L positions,
O fills the third and the target solves. Otherwise d≤1; and if d=1,
all disjoint sources must be Z34.

Write z34 for the Z34 count. We now try opposite12|34, omitting0:

    A:13,14;  F:23;  O:24;

then fill31,32,41,42 from R,E,Z34. E and Z34 see all four positions,
while R sees41,42. This works whenever

    f>0,        e+z34≥2,        r+e+z34≥4.

The last inequality always holds under the remaining assumptions.
If d=1, all disjoint sources are Z34, giving r+e+z34=8−f≥5.
If d=0, it is at least9−f−z≥4.

If f=0, the count bounds force d=1,r=e=3,z=2, with both disjoint
sources Z34. Assemble rectangle01|34 using four A forward, O at41,
E at31, and the two Z34 at30,40.

Finally suppose e+z34<2. This cannot happen when d=1, since then
e+z34=8−r−f≥2. When d=0, we have e≥1, and the bounds force
e=1,z34=0,r=f=3,z=2. The two disjoint sources cannot match two L
positions, so both are B or Z24; a Z23 together with either would
give a two-matching. Both B and Z24 contain21,40,41. Assemble
rectangle01|24 with four A forward, O at20, the two disjoint sources
at21,40, and one R at41.

All cases are soluble. This proves the theorem.

## Cumulative consequence

Together with the preceding mixed four-class proofs, this establishes:

> A mixed diffuse fourteen-cube failure has every adjacent
> tricoloured-corner class count at most three.

The result is elementary and independent of the finite eight-cube
lemma for high opposite-source counts. It does not close the remaining
mixed cases in which all adjacent class counts are at most three.
