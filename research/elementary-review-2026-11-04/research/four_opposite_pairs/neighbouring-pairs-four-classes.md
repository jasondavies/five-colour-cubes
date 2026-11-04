# Two neighbouring opposite pairs and four distinct adjacent classes

**Theorem.** Suppose opposite varieties P,Q share two undirected corner
edges. Two copies of P, two copies of Q, and one cube from each of any
four distinct adjacent tricoloured-corner classes assemble an opposite
target, using all eight cubes.

Consequently, four opposite cubes of profile2,2 with neighbouring
varieties, together with ten adjacent cubes of class multiplicity at
most three, always assemble: ten such cubes occupy at least four
classes, so select one cube from four of them.

## 1. The three blocks

Let I=P∩Q, J=P\Q, K=Q\P, with undirected edges represented by both
corner directions. Each block has two edges and four directed corners.
The three opposite targets are

    P=I∪J, Q=I∪K, T=J∪K.

Their union is either K4 or K2,3. This line geometry is proved in
`../opposite_small_lemma/two-neighbouring-opposite-pairs.md`.

It suffices to match the four adjacent sources to two distinct corners
in each of two blocks. On P, for example, the two Q copies fill the
remaining two I corners and the two P copies fill the remaining two J
corners. On Q the roles reverse; on T, the two P copies fill its two
remaining J corners and the two Q copies fill its two remaining K
corners.

An adjacent cut has at most two corners in each block and meets each
opposite target in two or four corners. Its three block counts are
therefore precisely

    (1,1,1), (2,2,0) and its permutations, or (2,2,2).

Indeed the three pairwise sums must be2 or4. This forces all block
counts to have the same parity, giving exactly those possibilities.

On a chosen two-block target call a source high if it has two corners
in each block. A source that is not high either has one corner in each
block or two corners confined to one block.

## 2. Two elementary allocation facts

**Two high sources.** Two high adjacent sources, together with any
other two adjacent sources, can fill two corners in each block.

If the other two sources can choose a corner in different blocks,
make those choices and use the high sources at different corners in
the respective blocks. Each high source has two choices in each
block. Otherwise the other two sources are both confined to the same
block. Each has two corners there, so they can choose different
positions; use the high sources at two different corners of the
other block.

**One high source.** One high adjacent source and three other sources
can fill two corners in each block, except possibly when either:

1. all three other sources are confined to the same block; or
2. each of the three has one corner in each block and their two-corner
   patterns are identical.

For completeness, suppose there is just one high source. If two of
the other sources are confined to one block, assign them distinct
corners there; unless the third is also confined there, it and the
high source occupy different corners of the other block. If two
sources are confined to different blocks, use the third source in
one block, the confined source there at its other corner, and the
remaining confined source and high source in the other block.

If just one source is confined to a block and the other two have one
corner in each block, use those two in the opposite block if their
corners differ. If those corners agree, use one of them there and the
other in the first block; the confined and high sources supply the
other corner of each block. Finally, if all three have one corner in
each block and their patterns are not identical, two have different
corners in one block. Use them there, the third source in the other
block, and the high source at a different corner of that block.

## 3. If any adjacent source is high somewhere

Choose a line target on which that source is high. Two high sources
solve by the first allocation fact, so assume there is exactly one.

Exception2 in the second fact cannot occur for three distinct
adjacent classes. A two-corner intersection with an opposite target
determines at most two adjacent classes. If the corners lie on
adjacent edges, their directed-star pattern fixes the cut on the four
target vertices and the fifth colour must join its singleton side.
If they lie on opposite edges, the cut on the four vertices is fixed,
and the fifth colour has at most two choices of side.

If exception1 occurs, the three sources confined to one block must
have profile(2,0,2) or(0,2,2), relative to the chosen two-block target.
They are all high on another line target. The two-high allocation
fact applies there. Thus this case is solved.

## 4. All four sources have profile(1,1,1)

We use two small geometric facts about these classes.

* At most three profile(1,1,1) classes contain any fixed corner of
  a block.
* At most two classes have any fixed two-corner intersection with a
  line target, as proved in Section3.

For the first fact, on a K4 line a profile(1,1,1) cut is a directed
star on the four vertices. A fixed corner u→v belongs only to the
outgoing star at u and the incoming star at v, so at most two classes
occur. Each star has a unique extension to a2|3 cut on five colours.

For a K2,3 line, the blocks are the two-edge stars at the three
vertices on its size-three side. A profile(1,1,1) cut separates the
two vertices on the other side. Fixing one directed block corner
determines their sides and the side of that block's centre. The
remaining two centres have exactly three allowed placements making
the side sizes two and three. Thus at most three classes contain
the corner.

Choose any two blocks and write the four source patterns as pairs
(x_i,y_i), one corner in each block. Neither coordinate is constant,
since the four source classes are distinct and at most three classes
contain a fixed block corner. No three pairs are identical, since
at most two classes give a fixed two-corner target intersection.

These conditions imply that two sources can choose different x
corners while the other two choose different y corners. Here is an
elementary proof. Choose x_1≠x_2. If y_3≠y_4, we are done.
Otherwise write y_3=y_4=y and suppose no suitable allocation exists.
For i=3,4, if x_i differs from both x_1,x_2, applying the supposed
failure to the pairs(1,i) and(2,i) forces y_1=y_2=y, a contradiction.
Thus x_3,x_4 each equal x_1 or x_2. If they differ, those same pair
choices again force y_1=y_2=y. If they agree, say x_3=x_4=x_1,
the pair(2,3) forces y_1=y, giving three identical pairs at indices
1,3,4, again a contradiction. The other case is symmetric.

The resulting allocation has two different corners in each block.
The opposite pairs fill the remaining positions as in Section1.
This finishes the theorem.

## 5. Corollary for any four capped opposite sources on one line

**Corollary.** Four opposite sources drawn from the three varieties
P,Q,T of one line, with each variety occurring at most twice, together
with four distinct adjacent classes assemble an opposite target.

The proof above finds a line target with two adjacent holes in each
of its two blocks. For any selected line target, each of the four
opposite sources is either universal or confined to one whole block.
At most two source copies are confined to either block, because such
copies all have the same opposite variety. Fill their positions
first within the two residual corners of that block, then let the
universal sources fill the remainder. Thus the same adjacent
allocation proof works for every capped four-source inventory on a
line, including profile2,1,1.

## Scope and verification

This proof uses only the two possible line geometries, the three
block-count profiles, and the explicit allocation arguments above.
It does not require a classification of four-opposite inventories or
any assumptions on the repeated colours of the adjacent sources.

An independent finite check can fix either line type and test all
binom(20,4)=4,845 distinct adjacent-class selections. All are solved
using one of the three displayed line targets. This is corroboration
of the proof, not a premise.
