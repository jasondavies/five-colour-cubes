# Five opposite cubes and nine adjacent cubes

## Result

**Theorem.** Five opposite-repeat five-colour cubes, with no variety
occurring more than twice, together with nine adjacent-repeat cubes,
with no tricoloured-corner class occurring more than three times, contain
eight cubes that assemble an opposite-repeat target.

This is an elementary proof. Its ingredients are a replacement lemma,
the previously written five-opposite grid constructions, and the
nine-distinct-class theorem. No exhaustive inventory list is used.

The essential new observation is that the third copy of an adjacent
class in the older proofs can be introduced temporarily. All the
subsequent constructions use only two actual copies of that class.

## 1. Replacing the third copy

**Replacement lemma.** Let O be any five opposite sources and let A
be an adjacent tricoloured-corner class. If O together with three
copies of A assemble an opposite target, then O together with two
copies of A and any adjacent source B also assemble an opposite
target.

**Proof.** In the given eight-cube assembly, the three A copies occupy
corners on three distinct undirected target edges: an adjacent cut
contains at most one direction of each edge. Every adjacent source
meets an opposite target on at least two underlying edges. Therefore
B has a compatible corner on one of the three edges occupied by A.

If its direction agrees with the A corner, replace that A copy by B.
Otherwise swap the two directed corner positions on that one target
edge. Its other position was occupied by an opposite source, since
the three A positions lie on distinct edges. That opposite source
supports both directions, so it remains compatible. Put B at the
reversed A position and leave the other two A assignments untouched.

This is an operation on the corner assignment. Each chosen source
can then be properly rotated to its assigned corner. It does not
assert a reflection of any physical cube. The repeated colours within
adjacent classes do not affect compatibility with an opposite target.
∎

## 2. The geometric constructions that remain after replacement

Fix A=C(01), with its six corners in a two-by-three grid. Colour
permutation and, if necessary, reversal of all directed corners reduce
any adjacent class to this form.

Each opposite variety meets this grid in two positions in different
columns, or in a complete two-column rectangle. Each such pattern
determines its variety uniquely.

If the five opposite sources match four positions of a two-column
rectangle, they assemble with three copies of A: four fill the reverse
rectangle, and the fifth plus the three A copies fill the forward
rectangle. The replacement lemma then gives an assembly with two
actual A copies and any adjacent helper.

Otherwise all three rectangle ranks are at most three. Any five grid
positions contain two complete columns, so a matching to five positions
would give a matching of a complete rectangle. Thus the full grid
rank is at most four. Hall's theorem gives a set H of three or four
grid positions satisfying

    |H| + number of opposite copies with pattern not contained in H ≤ 4.

The elementary consequences of this cover have already been proved
in the five-opposite notes. The relevant conclusions, including the
number of A copies they actually use, are as follows.

### At most one doubled opposite variety

The opposite profile is 1,1,1,1,1 or 2,1,1,1. Either all five patterns
lie in a four-position shape with column sizes 2,1,1, or four source
copies lie on three positions in three different columns, with a
fifth outside. In the latter case the four inside copies are 2P+Q+R,
where P,Q,R form a line of neighbouring varieties.

In either case there is a central target T such that:

1. A meets T in exactly two directed corners a,b;
2. after a,b are removed, the five opposite sources can fill any five
   of the remaining six positions.

The proof is the Hall calculation in Sections 1–3 of
`../opposite_small_lemma/five-opposites-low-repetition.md`.
It uses only the grid cover, not a third physical A cube.

At most two adjacent classes have their entire T-intersection inside
{a,b}. One of those classes is A. Any adjacent helper outside these
at most two classes supplies a third corner c. Use two A copies at
a,b, the helper at c, and the five opposite sources at the remaining
positions.

### Two doubled neighbouring opposite varieties

The opposite profile is 2P+2Q+R, with P,Q sharing two undirected
edges. The explicit neighbouring-pairs construction assembles with
two A copies and any helper from a different class. See
`../opposite_small_lemma/five-opposites-neighbouring-pairs.md`.

### Two doubled nonneighbouring opposite varieties

Here P,Q share one undirected edge. The grid cover leaves one
overlapping pattern shape or three disjoint pattern shapes. Their
explicit targets and allocations are in Sections 2–3 of
`../opposite_small_lemma/five-opposites-nonneighbouring-pairs.md`.

Every final construction uses exactly two A copies, all five
opposite sources, and one adjacent helper meeting a specified rescue
set E. In each case at most two adjacent classes avoid E, and A is
one of them. The third A copy occurs only in the initial rectangle
construction already covered by the replacement lemma.

For the overlapping shapes, E consists of five remaining positions
after two A copies and the single opposite source are assigned. The
two opposite pairs fill any four of these five. For the disjoint
shapes, E is the union of the helper positions in two explicit
completions; it consists of two bidirected edges and a further directed
edge joining their components. Keeping both endpoint pairs together
and respecting the remaining direction permits at most two adjacent
cuts. These include A, which has no corner in E.

The audit and adapted proof are in
`../five_opposite_profiles/two-doubles-fourteen.md`.

## 3. A useful nine-cube strengthening

The preceding argument proves the following more general statement.

**Helper lemma.** Let A,B,C be three different adjacent
tricoloured-corner classes. Five capped opposite sources, two copies
of A, one source in B, and one in C contain an opposite assembly.
Indeed, at least one of the eight-cube subpools O+2A+B and O+2A+C
assembles.

If O+3A assembles, the replacement lemma applies to either helper.
Otherwise use the grid-cover constructions above. In the low-repetition
and nonneighbouring cases, at most two classes avoid the rescue set,
one of which is A. Thus B and C cannot both avoid it. The neighbouring
case accepts either helper directly. Every construction uses the two
actual copies of A and only one helper. ∎

## 4. Proof of the requested fourteen-cube theorem

If the nine adjacent cubes belong to nine different classes, the
elementary nine-distinct-class theorem gives an opposite assembly;
see `nine-distinct-hall-proof.md`.

Otherwise some class A occurs at least twice. Since the nine adjacent
sources have class cap three, at least three classes occur. Choose sources from
two other distinct classes B,C. The helper lemma gives an assembly
using the five opposite sources, the two A copies, and one of those
helpers. ∎

The statement was originally recorded with adjacent class cap two.
The same proof gives cap three: it needs only a doubled class and
two other occupied classes. This strengthening was noted on
4 November 2026 while assembling the direct fifteen-cube proof.

## 5. Consequences and exact scope

Together with the earlier adjacent-triple and mixed concentration
lemmas, this closes the full opposite-total-five branch of the
fourteen-cube problem when every opposite variety has multiplicity
at most two.

For fifteen cubes with five or six opposite sources, once opposite
variety cap two and adjacent class cap three have been established,
select five opposite sources and nine adjacent sources. The theorem
applies directly. Thus both of these opposite totals are covered by
the same argument in `fifteen-elementary-proof.md`; the separate
six-opposite theorem is not needed for that particular conclusion.

This local theorem does not classify fourteen-failures with fewer
opposite sources. The current global proof status is recorded in
`../NEXT_STEP.md` and `fifteen-elementary-proof.md`.

Combining this theorem with the earlier concentrated-opposite and
large-opposite arguments gives the following statement without
multiplicity assumptions:

> **Corollary.** Every fourteen-cube pool containing at least five
> opposite-repeat cubes assembles a five-colour target.

Indeed, a fourteen-failure with an opposite variety occurring at least
three times has opposite total exactly three or four, by the elementary
classifications in `o4-elementary.md` and `o3-covers-guide.md`. Thus a
failure with at least five opposite sources would have opposite cap
two. Totals at least six are already excluded by the previous
large-opposite arguments. At total five, an adjacent class occurring
at least three times is excluded by the earlier concentration and
triple-class lemmas; otherwise the present theorem applies. ∎

The stronger universal eight-source statement O+2A+B for every B≠A
is not needed here. It has now been proved separately for opposite
profile 2,2,1 in
`../five_opposite_profiles/two-pairs-two-adjacent-one.md`, including
four explicit exceptional matchings. The other profiles are not
asserted to have that stronger elementary proof in this checkpoint.

## Independent audit

The complete proof and the nine-source helper lemma received a
separate mathematical audit, recorded in
`../five_opposite_computation/five-target-proof-audit.md`.
Its small geometric checker verifies the fifteen grid patterns,
the two four-position and two three-position normal forms, 72 line
completions, 180 two-corner avoiding-class assertions, all four
nonneighbouring normal forms, 46 rescue sets, and 370 displayed
helper assignments. All checks passed. They are corroboration of
the written proof, not inventory-enumeration premises.
