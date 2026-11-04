# Guide to the complete three-identical-opposite branch

Assume a fourteen-failure contains three copies of an opposite variety.
The four-copy theorem already handles any opposite variety occurring
four times; hence assume each opposite multiplicity is at most three.
Normalize the three copies to X=O(0;12|34).

Hall's theorem supplies a cover C of at most four of X's eight corners,
with at least7+|C| nonanchor copies whose intersections with X lie in C.
The two-corner case is impossible by the established caps. The five
three-corner types are eliminated in Section6 of
`../invariant_structure/elementary_refinements.md`. This uses the
explicit opposite-triangle extension lemmas from its preceding section.

If |C|=4, all eleven other sources belong to the indicated cover family.
The ten symmetry types are listed below. A bit mask is only an index
for the displayed corner subset, in order13,14,23,24,31,32,41,42.

| Cover corners | Mask | Orbit size | Hand argument |
|---|---:|---:|---|
|13,14,23,24|15|2|`o3-butterfly.md`: exactly the5,3,3 family survives |
|13,14,23,31|23|8|`../invariant_structure/o3_masks23_53_102_hand.md` |
|13,14,24,31|27|16|`../invariant_structure/o3_mask27_hand.md` |
|14,23,24,31|30|8|`../invariant_structure/o3_masks30_51_hand.md` |
|13,14,31,32|51|8|`../invariant_structure/o3_masks30_51_hand.md` |
|13,23,31,32|53|4|`../invariant_structure/o3_masks23_53_102_hand.md` |
|14,23,31,32|54|16|`../robust_route/o3-mask54-hand-proof.md` |
|14,24,31,32|58|4|`../support_families/o3-reverse-family.md`, after symmetry |
|14,23,32,41|102|2|`../invariant_structure/o3_masks23_53_102_hand.md` |
|13,24,32,41|105|2|No source has its X-intersection contained in this cover |

The orbit sizes sum to70=binom(8,4). This is a geometric classification
of four directed arcs on a bidirected four-cycle, not an enumeration
of cube inventories. One can list it by the number of underlying edges
selected in both directions: zero, one, or two.

Only the first cover family admits failure. Its hand analysis forces
three opposite copies, high adjacent counts5 and3, and one low adjacent
class of size3, with a unique repeated-colour refinement. There are
eight such configurations for each of the two covers in this orbit,
and fifteen choices of X: 8·2·15=240 labelled failures.

Together with the four-copy theorem, this proves that any
fourteen-failure containing an opposite variety at multiplicity at
least three is one of the two observed opposite-containing families.
Both have W=36.

The arguments for covers53 and54 use the existing eight-plus-three
missing-pair lemma from the paper. All other inputs are established
in this bundle or are the elementary directed-corner geometry.

