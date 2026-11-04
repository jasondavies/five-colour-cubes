# Independent audit: pair compression, intersecting cuts, and the nine-cube core

4 November 2026

**Result: passed.** The root's replacement principle and three-family
containment proof in
`../three_opposite_root/pair-compression-and-intersecting-cuts.md`
are valid. The conditional reduction has exactly the stated dependency
on the three-opposite fourteen-source theorem. Sections 1–2 of
`../three_opposite_root/repeated-colour-closures.md` also have complete
and valid hand proofs.

This was a mathematical audit of the arguments and all relevant
source assignments. No inventory search was used.

## 1. Compressing two disjoint adjacent cuts

For A=C(01), an adjacent cut disjoint from A is exactly one of
C(234), C(23), C(24), C(34). This also follows directly from the
signed-pole rule checked below. For B=C(ij), i,j in234, the cut A
contains the forward half of the opposite target01|ij and B its
reverse half. C(234) contains the reverse half for every such i,j.
Thus the opposite variety's complete corner set lies in A∪B.

Removing both actual sources before introducing the one virtual
opposite source is essential and is done explicitly. If an assembly
uses the virtual source at a corner, one of the two removed actual
sources supplies that same oriented corner. It is free to be used,
since neither removed source occurs elsewhere in the virtual pool.
Only one corner is assigned to a source cube, so no simultaneous
compatibility condition is needed. If the virtual source is unused,
the original actual pool already contains the assembly.

This remains valid when the target is adjacent: a virtual opposite
source can only have been used at a tricoloured target corner, so its
replacement never needs a bicoloured corner.

## 2. The conditional fifteen-to-fourteen reduction

Two opposite and thirteen adjacent sources become three opposite
and eleven adjacent sources after the compression, exactly fourteen
in total. Adjacent class caps can only decrease. The only way an
opposite variety can now occur more than twice is for all three
opposite sources to be identical.

In that exceptional case the earlier concentrated-opposite
fourteen-failure classification forces adjacent class sizes5,3,3,
which contradicts the surviving class cap three. Otherwise the
stated three-opposite theorem applies. The replacement argument
then returns an assembly in the actual fifteen-pool.

The root note correctly labels this numerical consequence as
conditional until the complete three-opposite theorem is available.
Neither its replacement proof nor its support classification assumes
that theorem.

## 3. Signed pole pairs and the three containing families

For two positive cuts C(P),C(Q), their corner intersection is nonempty
exactly when the two pole pairs meet: its tails lie in P∩Q and its
heads outside P∪Q. The same conclusion holds for two negative cuts
by reversing all directions.

For a positive cut with pole pair P and a negative cut with pole pair
Q, their common corners have tails in P\Q and heads in Q\P. Since
P,Q both have size two, the intersection is empty exactly when P=Q.
Therefore a pairwise-intersecting signed cut family is precisely two
intersecting edge families with no edge used in both signs.

An intersecting edge family is contained in a star or a triangle.
The root's proof via ab,ac and the possible edge bc is complete,
including singleton or empty families by choosing a containing star.

Every combination of the two containing shapes is covered:

- Two edge-disjoint triangles on five vertices intersect in exactly
  one vertex and give the butterfly.
- A triangle and a star whose centre lies outside it extend to the
  star-and-triangle family.
- If that centre is in the triangle, the permitted star edges go to
  its two outside vertices; they extend to a second triangle meeting
  the first only at the centre, giving a butterfly containment.
- Different star centres share only their joining edge. Giving this
  edge its existing sign, or either sign if absent, permits a full
  four-edge star of one sign and the other three-edge star.
- Equal centres with both signs of size at least two force exactly
  two disjoint leaf pairs; completing both to triangles gives the
  butterfly. If one sign has at most one edge, its other endpoint
  can serve as a different centre; an empty family permits any
  distinct centre.

All extensions preserve the absence of a pole edge in both signs.
The displayed three families therefore give a valid containing
classification, not merely a list observed in a search. In
particular their maximum size seven gives the claimed support bound.

## 4. Two intersecting own-looped triples

An own-loop matching is a tricoloured-corner statement, so any two
physical copies of its class can be designated as the reserved pair.
If two of three copies have the same repeat, they fill the two
bicoloured corners and the loop matching completes their target.

Otherwise each triple has all three repeats allowed outside its pole
pair. Two three-element repeat sets among five colours intersect.
If the pole pairs meet, a shared-repeat source of the second class
can supply the shared pole of the first target, while a source of
the first class supplies its other pole. In the loop matching,
restoring the other reserved first-class source compensates for
removing the selected second-class source whenever it was used.
The restored source is universal on the six tricoloured corners of
that target, so the replacement is valid.

Every source counted in the new matching remains distinct. This
proves the lemma. Three own-looped triples include two meeting pole
pairs because three pairwise disjoint two-element pole pairs would
require six colours.

## 5. The nine-cube construction

For five distinct colours a,b,c,d,e, write
A=C(ac), B=C(bc), H=C(abc). An opposite source containing edge ab
supplies both ab and ba. After two A reservations, the root's row

    remaining A:cb;  two B:cd,ce;  two H:ad,ae;  O:ab

is exactly A's six corners. It uses one of the one remaining A,
two of the three B, both H, and the one O. The corresponding row

    remaining B:ca;  two A:cd,ce;  two H:bd,be;  O:ba

is exactly B's six corners, with equally valid source counts.
Both triples are own-looped and their pole pairs meet at c. Section 4
therefore gives an assembly. Reversing all listed cuts reverses
the tricoloured assignments, and the opposite source still supplies
the needed ab direction; pole pairs and allowed repeats are unchanged.

Thus the nine-source theorem is valid without any further condition
on the opposite variety beyond containing ab.

## 6. A useful retrospective strengthening

Take a=0,b=1,c=4,d=2,e=3. The new lemma gives

    O + 3C(04) + 3C(14) + 2C(014),

for any opposite source O containing01. This strengthens the
eleven-source core used in the previous four-opposite alternating-path
proof: its two extra Q sources are unnecessary. The two own-loop
assignments can be written particularly simply as

    C(04):41; C(14):42,43; C(014):02,03; O:01,
    C(14):40; C(04):42,43; C(014):12,13; O:10.

This is a consequence of the audited nine-source lemma, and does not
alter or weaken any dependency in the earlier proof.
