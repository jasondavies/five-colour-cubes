# Six copies in one adjacent tricolour class

This gives a self-contained hand proof of the concentration lemma used
elsewhere in the research notes.

**Lemma.** Every collection of fourteen five-colour cubes containing at
least six cubes from one adjacent tricoloured-corner class is soluble.

Write C(S) for the directed cut S→Sᶜ, where |S| is two or three. Its
pole pair is its two-element side. Its three varieties are indexed by
their repeated colour, which lies outside that pair. Two copies with
the same repeat supply both bicoloured corners of either orientation
of the cut with that pole pair.

Normalize the chosen class to A=C(01). Three elementary observations
will be used.

* The four adjacent classes disjoint from A in tricoloured corners are
  B=C(234), C=C(23), E=C(24), F=C(34). No opposite variety is disjoint
  from A. Four A and four copies of any one of these classes form an
  opposite target, by using four arcs in each direction between
  {0,1} and a suitable two-element subset of {2,3,4}.
* The reverse cut B has six arcs grouped into three pairs q→{0,1},
  q∈{2,3,4}. A B source sees all three pairs, while C,E,F each miss
  one pair. Thus at least six sources from B,C,E,F, with each of
  C,E,F occurring at most three times, match all six arcs of B.
  Hall is immediate: a set of arcs confined to one pair has at
  least three neighbours; a set meeting two pairs sees every source.
* Each intersection of another class with A has size0,1,2,4, or6.
  An intersection of size1 determines a unique adjacent class.
  Indeed, for an outset S the intersection has size
  |S∩{0,1}|·|{2,3,4}\S|, which is one precisely when S consists
  of one of0,1 and two of2,3,4. Opposite sources have intersection
  size2 or4.

First suppose A occurs at least eight times. Reserve two copies with
the same repeated colour for the bicoloured corners and six further
copies for the tricoloured corners. If A occurs seven times and some
outside source shares a tricoloured corner with A, reserve a same-repeat
pair, use five A and that source for the six tricoloured corners.
Otherwise all seven outside sources lie in B,C,E,F. If one of those
classes occurs four times, the first observation solves. If not, the
second observation supplies the six tricoloured corners of B; two A
copies with the same repeat supply B's bicoloured corners. Hence no
failure has a class of size at least seven.

It remains to consider exactly six A copies. Reserve a same-repeat
pair. If two outside sources can be matched to two distinct A corners,
the four remaining A copies complete the target. Suppose this is not
possible. Let z be the number of outside sources disjoint from A.
Each of their four classes has at most three copies, or the first
observation solves. If z≥6, the second observation solves using two
A for the bicoloured corners of B.

Thus z≤5. At least three of the eight outside sources meet A. Since
they cannot match two distinct A corners, they all meet A in the
same single corner. By symmetry that corner is13, and all these
sources belong to D=C(124). Write m=8−z for their number. The
previous paragraph excludes m≥7, so 3≤m≤6.

The intersections of B,C,E,F with D are respectively

    B: {20,40}; C: {20}; E: {20,23,40,43}; F: {40}.

All are nonempty and avoid13, the corner supplied by A.

* **m=6.** Reserve a same-repeat D pair. Four remaining D, one A
  for13, and any disjoint-from-A source for a different D corner
  fill its six tricoloured corners.
* **m=5.** If two of the three disjoint sources match different D
  corners, use those two, one A for13, and three D for the remaining
  corners, after reserving a D pair. This fails only if all three
  disjoint sources are C, or all three are F. In the C case assemble
  the opposite target ±{02,03,12,13}: four A supply02,03,12,13;
  one D supplies20; and three C supply21,30,31. The F case is
  symmetric, using ±{03,04,13,14}.
* **m=4.** If at least three of the four disjoint sources are E,
  reserve a D pair; the other two D, one A for13, and three E for
  three of20,23,40,43 complete the D target. Otherwise at most
  two are E. Three of the disjoint sources can then match21,30,31:
  the first corner sees B,C,E; the last two see B,C,F; the latter
  pool has at least two copies, the former at least one, and the
  union has four. Together with four A and one D for20, this
  assembles ±{02,03,12,13}.
* **m=3.** There are five disjoint sources and each class count is
  at most three. The same two pools have respectively at least
  two and two sources, so three sources match21,30,31. Four A
  and one D again complete the same opposite target.

Every case gives an assembly, proving the lemma.

