# Three distinct opposite cubes and eleven adjacent cubes

4 November 2026

**Status: elementary proof; all component proofs and the joining
argument passed full independent root audits.**

**Theorem.** Three pairwise distinct opposite-repeat five-colour
cubes, together with eleven adjacent-repeat cubes whose
tricoloured-corner class counts are at most three, contain eight
cubes assembling a five-colour 2×2×2 cube with monochromatic faces.

The conclusion permits an adjacent target. In particular the
common-corner lemma used below proves an assembly by repeated-colour
arguments; the stronger computational observation that an opposite
target always exists is not needed or asserted as proved here.

## 1. The geometric inputs

An adjacent class is a directed cut C(S)=S→Sᶜ on five colours,
where |S| is two or three. An opposite variety is a four-cycle and
supplies both directions of each of its four underlying edges.

On an opposite target, every adjacent class has two or four corners,
on distinct underlying edges. At most two adjacent classes have
their entire intersection inside two specified positions, and at
most three inside three specified positions. These are the elementary
cut facts in `../four_opposite_lowrep/four-distinct-opposites.md`,
Section 1.

Call an opposite source high on a target if it meets at least two
underlying target edges. The following two four-cycle facts were
proved independently of the numerical four-opposite theorem in
`../four_opposite_root/common-high-targets.md`, Section 3:

1. Any three distinct opposite varieties have a common high target.
2. On a fixed target, a specified two-edge intersection determines
   its distinct high source variety uniquely.

The first follows by using the line of a neighbouring pair, or by
closing a four-cycle through two edges of a missing three-edge path
when all three pairs are nonneighbours. The explicit four-row
classification is given in that note.

Three additional elementary lemmas are used:

- `global-zero-edge.md`: if all eleven adjacent sources avoid one
  underlying edge, the pool has an opposite assembly;
- `rectangle-family.md`: if the adjacent sources are all confined
  to one directed half of a common high target, the pool assembles;
- `../three_opposite_double/common-corner-eleven-hand.md`: eleven
  capped adjacent sources containing one common directed corner
  already assemble, without using any opposite source.

## 2. The adjacent matching dichotomy

On any fixed opposite target T, the eleven adjacent sources either
have matching rank at least five, or all their intersections are
contained in four directed positions.

Indeed, a Konig cover of size at most four with three corner
vertices covers at most nine source copies through those corners,
and at most one other source through its source vertex. A cover
with two corner vertices covers at most six copies and two extras.
With at most one corner vertex, every adjacent source requires a
source vertex, since it meets at least two positions. None covers
eleven sources. Thus any cover of size at most four must consist
solely of four corner vertices.

Suppose, for contradiction, that the whole pool fails. The first
additional lemma lets us assume every underlying edge occurs in
the adjacent pool. Also nine adjacent sources cannot all avoid
two underlying edges: meeting edges have only two reverse avoiding
classes, while disjoint edges have four avoiding classes in two
orientations; nine copies then yield an assembly with at most one
opposite source. This nine-avoider argument is written in
`../four_opposite_root/common-high-targets.md`, Section 1.

Consequently any pair of underlying edges has at least three
adjacent-source neighbours.

## 3. A fully supported common high target

Choose a common high target T, and first suppose the union of the
three opposite varieties covers every edge of T.

### Adjacent matching rank at least five

The four underlying target edges can be matched to four distinct
adjacent sources. Every single edge has a neighbour; every pair
has at least three neighbours; and every three-edge set meets all
eleven sources, because each adjacent class uses at least two of
the four target edges. Hall proves the matching.

Choose a compatible directed position on each edge. Extend this
four-position independent set to five matched positions by an
augmenting path. The five positions still cover all four underlying
edges. Their three-position complement therefore uses three
distinct underlying edges.

The three opposite sources fill this complement. A single edge
has a neighbour by full support. Any two edges have at least two
neighbours: only the unique high variety whose intersection is
the complementary pair can avoid them. Any three edges meet all
three high sources. These are all Hall inequalities needed for
three positions on distinct edges.

### Adjacent matching rank at most four

All adjacent target intersections lie in four positions H, by
Section 2. Since every underlying edge is covered, H contains
exactly one direction on each of T's four edges. Regard H as an
orientation of the square.

A directed cycle is impossible: a cut confined to its directions
would have to place all four vertices on the same side. That is
incompatible with a 2|3 cut of five colours.

If the square orientation has two sources and two sinks, it is
alternating, and H is one directed half of an opposite target.
The rectangle-family lemma applies.

Every other acyclic orientation of a square has a unique source a
and a unique sink b. A cut whose target intersection is confined
to H has its outset downward closed along this orientation. Its
restriction to the four target vertices is nonempty and proper,
again because a whole side cannot contain four vertices. Such a
set contains a and excludes b. Thus every adjacent source contains
the same directed corner ab, whether or not ab is an edge of T.
The common-corner eleven-source lemma applies.

Both matching ranks therefore contradict failure. This closes the
fully supported common-target case.

## 4. The unsupported common target

If the common target is not fully supported, its three distinct
high source patterns are the three two-edge subsets of three
target edges. Indeed there cannot be only two supported edges,
by uniqueness of a two-edge high pattern. None of the sources is
T, so each meets exactly two edges, and distinctness gives all
three pairs. The supported edges form a three-edge path.

There is only one unmarked geometric form. A convenient
representative is

    O60={13,14,23,24},
    O64={02,04,23,34},
    O68={01,03,14,34},

on common target O61={12,14,23,34}, whose edge12 is unsupported.
Every two-edge pattern determines its variety, so this normalization
leaves no hidden choice of opposite source.

The complete closure is `unsupported-triad.md`. If the adjacent
pool supplies both directions of12, extend those two positions
to a five-corner adjacent matching; the opposite sources fill any
three positions on the other three edges. Otherwise normalize the
absent direction to12. The three source varieties themselves are
used as candidate targets. Their possible Hall obstructions reduce
to seven rows on one target and five rows on each of the other two,
which are symmetric.

Each row requires all but at most k=0 or1 adjacent sources to lie
in a stated avoiding set. Three selected rows have common avoiding
set I satisfying |I|≤4−(k_1+k_2+k_3). The class cap makes every
choice with a positive k impossible for eleven sources. The only
zero-k intersections large enough are four-class common-corner
families, already solved by the common-corner lemma. The complete
small set-intersection certificate is displayed in that note.

Thus the unsupported target case also assembles, completing the
proof for three distinct opposite sources.

## Scope

This closes the opposite multiplicity profile 1,1,1 for the
fourteen-source target, and consequently for the direct fifteen-
source problem after discarding any one adjacent cube. It does not
by itself settle profile 2,1, nor the remaining totals of one or
two opposite sources.

The proof uses no inventory enumeration or repeated-colour search
as a premise. The small tables in the last branch are complete
Hall corner-set and set-intersection calculations, analogous to
the earlier nine-distinct-class Hall-table proof. No new Lean
formalisation is claimed.
