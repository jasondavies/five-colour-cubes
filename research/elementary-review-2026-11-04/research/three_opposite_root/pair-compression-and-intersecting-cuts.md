# Compressing a disjoint pair of adjacent cuts

4 November 2026

This note gives an elementary replacement principle and a three-family
classification. The three-opposite fourteen-cube theorem has now been
proved, so the reduction of the two-opposite fifteen-cube problem to
these three families is unconditional. The replacement principle and
family classification have also passed an independent mathematical
audit in `../three_opposite_distinct/audit-root-replacement-and-nine-core.md`.

## 1. Two disjoint adjacent cuts can represent an opposite cube

**Lemma.** If adjacent classes A,B have disjoint sets of tricoloured
corners, there is an opposite variety U whose eight corners belong
to A∪B. Consequently, an assembly using one virtual U source and
other actual sources can be converted into an assembly using one
of the two actual sources A,B, provided both were removed when U
was introduced.

Normalize A=C(01). Its disjoint adjacent classes are exactly

    C(234), C(23), C(24), C(34).

For B=C(ij), where i,j belong to {2,3,4}, take U with bipartition
01|ij. A supplies its forward half and B its reverse half. If
B=C(234), choose any two of 2,3,4 for i,j. Thus every corner of U
is available from at least one of the two actual sources.

The assembly assigns at most one corner to the virtual source.
Replace it by whichever of A,B supplies that corner, with a compatible
proper rotation. Both actual sources were absent from all the other
assignments, so source distinctness is preserved. If U was unused,
no replacement is necessary. Repeated colours of A,B are irrelevant,
since U is used only at a tricoloured corner.

## 2. Consequence for fifteen cubes with two opposites

The theorem in `../root/three-opposites-eleven-adjacent.md` proves
that any three opposite sources and eleven adjacent sources with
class cap three assemble, without an opposite multiplicity restriction.

Therefore any fifteen-pool with two opposite sources, thirteen adjacent
sources of class cap three, and a disjoint adjacent pair assembles.
Remove that pair and introduce U from Section 1. The new pool has
three opposite and eleven adjacent sources, and its adjacent class
caps have only decreased. Apply the stated theorem and convert the
resulting assembly back by Section 1. The three-identical-opposite
case is already included through the earlier concentrated classification.

Thus the remaining adjacent
support in the two-opposite fifteen-cube case is pairwise intersecting.

## 3. Pairwise-intersecting cut supports have three forms

Represent a cut of size-two outset by its positive pole pair, and
a cut of size-three outset by its negative pole pair (the two-element
complement). Two positive cuts are disjoint precisely when their
pole pairs are disjoint. The same holds for two negative cuts. A
positive and a negative cut are disjoint precisely when their pole
pairs are equal.

Therefore a pairwise-intersecting family of cuts consists of two
intersecting edge families F+,F− in K₅, with no edge in both families.
An intersecting family of edges is contained in a star or a triangle.
For if two edges are ab,ac and another does not contain a, that
other edge must be bc; every further edge meeting all three belongs
to the triangle abc.

We now show that every such signed family is contained, up to
relabeling colours and reversing all cuts, in one of these three:

| Type | Adjacent classes |
| --- | --- |
| Butterfly | C(01), C(02), C(12), C(123), C(124), C(012) |
| Two stars | C(01), C(02), C(03), C(04), C(034), C(024), C(023) |
| Star and triangle | C(01), C(02), C(03), C(04), C(034), C(024), C(014) |

If both signed edge families are triangles, their vertex triples
must meet in exactly one vertex: they cannot share an edge. Their
union is the butterfly form.

If one family is a triangle and the other lies in a star, consider
the star's centre. A centre outside the triangle permits extension
to the full four-edge star, giving the star-and-triangle form. A
centre in the triangle leaves at most its two edges to the two
outside vertices, since the other two edges already belong to the
triangle. Extend these two edges to the triangle on that centre and
the two outside vertices. This gives the butterfly form.

It remains that both families lie in stars. If their centres differ,
their stars share just the edge joining the centres. Assign that
edge to whichever sign already contains it, or to either sign if
it is absent. Extend that sign to its full star and the other to
its three remaining star edges. This is the two-star form.

If their centres coincide and both families have at least two edges,
each has exactly two, since the four incident edges cannot be used
twice. Complete each pair to a triangle on its two leaves and the
common centre. The triangles meet only at the centre and give the
butterfly form. If one family has at most one edge, choose the other
endpoint of that edge as its star centre; when the family is empty,
choose any different centre. The preceding distinct-centre argument
then applies.

This proves the three-family containment without enumerating cut
families. It also gives the support bound of seven classes.

## 4. Completed application

All three family lemmas are now proved and independently audited.
Their combination with the compression step proves that two opposite
cubes and thirteen adjacent cubes of class cap three always assemble.
The complete joining argument and component links are in
`../root/two-opposites-thirteen-adjacent.md`.

The exploratory script `intersecting_cut_families.py` reproduces the
three maximal family types. It is a diagnostic check; Section 3 is
the completeness proof.
