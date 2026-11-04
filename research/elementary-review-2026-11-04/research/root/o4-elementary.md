# Elementary classification of the four-identical-opposite branch

Status: a hand proof, using the six-in-one-adjacent-class lemma proved in
`six-adjacent-elementary.md`. The short shared-four-corners lemma is recalled below. This does not
classify failures with at most three copies of every opposite variety.

## Directed-corner notation

Colours are 0,1,2,3,4. Write `ab` for the directed tricoloured corner a→b.
An adjacent class is a cut C(S)={ab:a∈S,b∉S}, with |S|=2 or3. Its pole pair
is the two-element side P of the cut. There are three actual varieties in
this class, indexed by their repeated colour r∉P; their two additional
corners are (r,r,p), p∈P. Two copies having the same repeated colour can
therefore supply both bicoloured corners of that target class.

An opposite variety has eight tricoloured corners: both directions of a
K₂,₂ on four colours, omitting the repeated colour. Normalize an opposite
variety to O=±{13,14,23,24}, where ± adds reversed arcs.

We use the established fact that a fourteen-cube failure has at most five
copies in any adjacent class. Two adjacent classes sharing four tricoloured
corners have at most seven copies in total: if their total were at least
eight, choose a class with at least four copies, reserve two with the same
repeat for its bicoloured corners, use two remaining copies of that class
for its two private tricoloured corners, and fill the four common corners
from the remaining four copies of the two classes. If the other class has
fewer than four copies, the same assignment still works because all
remaining copies have all four common corners. (The six-in-one-class lemma
already handles the case of six or more copies.)

## Hall's cover form

If a target with eight corner types cannot be assembled from fourteen
sources, Hall's theorem gives a subset C of its corners, |C|=c≤7, such that
at least 7+c sources have all their target-compatible corners contained
in C. If the target variety itself occurs m times, these m copies do not
belong to that group, so c≤7−m.

Every five-colour source has at least two corners of an opposite target;
its intersection with that target has size 2,4, or8. This follows directly
from the directed cut/biclique descriptions.

## Five identical opposite copies suffice in a fourteen-pool

Suppose m≥5 copies of O occur in a failure. The Hall cover has c≤2, so c=2
and m=5. All nine other sources have their O-intersections contained in
this pair. Up to symmetry there are three nonempty possibilities:

1. A row or column pair, e.g. {13,14}: only the adjacent class C(01)
   is eligible, contradicting its bound five.
2. Two oppositely directed arcs on disjoint edges, e.g. {13,42}: two
   adjacent classes sharing four corners are eligible, contradicting
   their combined bound seven.
3. A reversed pair, e.g. {13,31}: precisely two other opposite varieties
   are eligible. Denote them U=±{01,04,13,34} and V=±{02,03,12,13}.
   If one occurs at least eight times it is itself an assembly; otherwise
   both occur at least twice. Four O, two U, and two V build
   T=±{12,14,23,34}: O supplies 14,41,23,32; U supplies 34,43; V supplies
   12,21.

Thus every opposite variety occurs at most four times in a failure.

## The four-copy theorem

**Theorem.** If a fourteen-cube failure contains four identical opposite
copies, its coarse profile is precisely O=4 and adjacent-class counts 5,5.
The two adjacent cuts share exactly one tricoloured corner.

Normalize the four copies to O. Hall gives c≤3. Covers with c≤2 are
impossible: the three eligible families above have capacities at most
5,7,8 respectively, whereas c=2 requires nine eligible sources. Thus
c=3, and all ten remaining sources have O-intersection contained in C.

There are five three-corner patterns up to the symmetries of O. Their
complete source lists are as follows. A cut is written by its source side.

| C | Eligible adjacent cuts | Eligible opposite varieties |
|---|---|---|
| 13,14,23 | 01; 124 | none |
| 13,14,31 | 01 | U,V |
| 13,14,32 | 01; 13; 013 | none |
| 13,24,31 | 023; 23 | U,V |
| 13,24,32 | none | none |

The five patterns account for 8,16,16,8,8 of the 56 three-subsets,
respectively. This small geometric table can also be checked without
enumerating subsets: first distinguish whether C contains a reversed arc
pair, then whether its remaining arcs share an endpoint.

### First row

There are only two eligible adjacent classes. Each has capacity five, so
their counts are 5,5. They share only the corner 13. This is the asserted
configuration.

### Second row

Let g,u,v be the counts of C(01),U,V. The bounds g≤5 and u,v≤4,
together with g+u+v=10, force both u,v positive and at least one of them
at least two. If u≥2, assemble T=±{12,14,23,34} using four O for
14,41,23,32; two U for 34,43; one V for 21; and one C(01) for 12.
If v≥2, instead use target T'=±{03,04,23,24}: four O supply
23,32,24,42; two V supply 03,30; one U supplies 40; and C(01) supplies
04. Both are assemblies, a contradiction.

### Third row

Let X=C(01), Y=C(13), Z=C(013), with counts x,y,z. The pairs X,Z and
Y,Z share four corners, so x+z,y+z≤7. Since x+y+z=10, x,y≥3.
At least one count is at least four and hence that class contains two
copies of one repeated variety. Reserve those two for its bicoloured
corners; the six tricoloured corners can be filled as follows.

* If x=5, three X supply 02,03,04, one Y supplies 12, and two O supply
  13,14. If x=4, then z≥1: two X supply 02,03 and one Z supplies 04;
  the other assignments are the same.
* If y=5, three Y supply 10,30,34, one X supplies 12, and two O supply
  32,14. If y=4, then z≥1: two Y supply 10,30 and one Z supplies 34;
  the other assignments are the same.
* Otherwise z≥4, and the bounds force (x,y,z)=(3,3,4). Three X supply
  02,04,12, one Y supplies 34, and two O supply 32,14.

Each assignment uses distinct physical cubes and yields an assembly.

### Fourth row

Let X=C(023), Y=C(23), with counts a,b, and let u,v count U,V.
We have a,b≤5, a+b≤7, u,v≤4, and a+b+u+v=10, hence u+v≥3.

If u,v are both positive, use four O for 14,41,23,32, one U for 43,
one V for 12, and any two adjacent copies for 21,34. Both X and Y have
both of these last corners. There are at least two adjacent copies
because u+v≤8. This assembles T=±{12,14,23,34}.

Otherwise, by symmetry take v=0 and 3≤u≤4. Build target U. Three U
copies supply 10,40,43; two further copies from U∪X supply 01,04;
one remaining adjacent copy supplies 34; two O supply 13,31. These
choices are possible because u+a=10−b≥5 and a+b=10−u≥6.

### Fifth row

There is no eligible source, so the row is impossible.

This proves the theorem. In this branch A=2·binom(5,2)=20 and
B=binom(4,2)=6, giving 3A−4B=60−24=36.

## Consequence for a hypothetical fifteen-cube failure

It cannot contain four copies of any opposite variety. Deleting one of
the other eleven cubes leaves a fourteen-failure, which the theorem
forces to have exactly the two five-copy adjacent classes and four O.
Restoring that cube and deleting a cube from a suitable one of those
classes cannot again give a 4,5,5 structure. Thus every opposite multiplicity
in a hypothetical fifteen-failure is at most three.

## A useful smaller opposite construction

Three O, two U, two V, and any eighth five-colour cube already assemble
an opposite target. The target T above needs O's four corners
{14,41,23,32}; the alternative T''=±{12,13,24,34}, with repeated colour
0 and partition 14|23, has O-intersection {13,31,24,42}. In both targets U and V supply
the four other corners (34,43,12,21). Every source intersects O in at
least two corners, so the eighth source meets at least one of these two
four-corner sets; it supplies that corner while three O supply the other
three.

