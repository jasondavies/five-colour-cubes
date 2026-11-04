# Two opposite cubes and thirteen capped adjacent cubes

4 November 2026

**Status: complete elementary proof.** The replacement principle,
geometric containment classification, and all three family lemmas
have passed independent mathematical audits.

## Theorem

Take two opposite-repeat five-colour cubes and thirteen adjacent-repeat
five-colour cubes. If every adjacent tricoloured-corner class occurs
at most three times, eight of these cubes assemble a five-colour
2×2×2 cube with monochromatic faces.

The two opposite varieties may coincide. Actual repeated colours
within each adjacent class are unrestricted.

## 1. Compress a disjoint pair when one exists

For an adjacent class, write C(S)=S→Sᶜ for its six directed
tricoloured corners, where the five-colour outset S has size two
or three. If two occupied classes A,B have disjoint corner sets,
their union contains all eight corners of an opposite variety U.

To see this, reverse all directions and relabel colours so that
A=C(01). Its disjoint classes are C(234), C(23), C(24), C(34).
If B=C(ij) for i,j in {2,3,4}, choose the opposite target 01|ij:
A supplies its forward half and B its reverse half. For B=C(234),
any such i,j works.

Remove one actual source in A and one in B, and add one virtual
source of variety U. The new pool contains three opposite sources
and eleven adjacent sources, with the adjacent class cap preserved.
The theorem in `three-opposites-eleven-adjacent.md` gives an assembly.

If the virtual source was used, replace it by whichever of the two
removed physical sources supplies its assigned corner. Both sources
were absent from the rest of the matching, so all eight assignments
remain distinct. If the virtual source was unused, the assembly is
already an assembly of the original pool. A virtual opposite source
can only have been used at a tricoloured corner, even when the target
is adjacent-repeat, so the replacement needs no bicoloured corner.

Thus any failing pool must have pairwise-intersecting adjacent
corner classes.

## 2. There are three containing families

Represent C(S) by a signed two-element pole pair: positive if
|S|=2, negative if |S|=3, using Sᶜ in the latter case. Same-sign
cuts are disjoint exactly when their pole pairs are disjoint;
opposite-sign cuts are disjoint exactly when their pole pairs coincide.

A pairwise-intersecting cut support is therefore two intersecting
edge families in K₅, with no edge used in both signs. An intersecting
edge family lies in a star or a triangle. Extending these two families
while preserving their disjoint edge sets gives, up to colour
permutation and simultaneous reversal, one of the following three
containing families:

| Family | Adjacent classes |
| --- | --- |
| Butterfly | C01, C02, C12, C123, C124, C012 |
| Two stars | C01, C02, C03, C04, C034, C024, C023 |
| Star and triangle | C01, C02, C03, C04, C034, C024, C014 |

The full containment proof, including equal star centres and partial
families, is Section 3 of
`../three_opposite_root/pair-compression-and-intersecting-cuts.md`.
It is a geometric proof, not a list obtained by enumerating supports.

## 3. Each family assembles

The following three hand arguments apply to arbitrary multiplicities
between zero and three summing to thirteen and to any two opposite
sources:

- **Butterfly:**
  `../elementary_alternative_next/butterfly-two-opposites-thirteen-adjacent.md`.
  Common-corner exclusions give four count inequalities. Explicit
  opposite targets reduce the remaining geometry to one configuration
  with two intersecting own-looped triples; their repeated colours
  complete an adjacent target.
- **Two stars:**
  `../three_opposite_distinct/two-star-two-opposites.md`.
  Either eleven adjacent cubes share a corner, or there are three
  copies of C01 and ten sources through corner 01. A six-position
  path matching and two short count inequalities cover every pair
  of opposite sources.
- **Star and triangle:**
  `../three_opposite_double/star-triangle-thirteen-adjacent-hand.md`.
  A six-position Hall lemma and a second direct matching force the
  only hypothetical failure to contain the globally reversed
  nine-source union-class construction. That construction assembles.

Consequently a pairwise-intersecting adjacent support also assembles.
Together with Section 1, this proves the theorem.

## Dependencies and scope

The three family lemmas depend on the common-corner eleven-source
lemma and local matching or repeated-colour arguments. They do not
assume this two-opposite theorem or the fifteen-cube threshold.
Only the compression step uses the three-opposite fourteen-cube
theorem. That theorem is independently proved in its distinct,
doubled, and concentrated opposite branches. The dependency chain
is therefore acyclic.

This proves the two-opposite branch required for N₅=15. It does not
assert that two opposite cubes and twelve adjacent cubes always
assemble; that stronger fourteen-cube question remains open in the
current elementary-proof programme.
