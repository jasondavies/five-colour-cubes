# Historical dependency outline for the direct elementary N5=15 proof

4 November 2026

**Superseded checkpoint.** Both review gates mentioned below have
since passed. The complete current synthesis and dependency order are
in `../root/fifteen-elementary-proof.md`. In its shorter final route,
opposite totals three and four both use the three-opposite theorem;
totals five and six both use the five-opposite helper theorem. The
older outline below is retained as a dated record of the joining
plan, not as the current list of open cases.

This is a logical assembly plan and dependency audit, not an assertion
that an unwritten or unaudited component has been completed. The last
star-and-triangle two-opposite family is still under separate work
when this note is written. The three-opposite2,1 joining argument has
been written and is undergoing its final root review.

The direct route does not require a classification of all fourteen-
cube failures or the global identity3A−4B=36.

## 1. Foundational lemmas

Start with the directed-cut/four-cycle model, compatibility under
proper rotations, Hall's theorem, and elementary repeated-colour
restoration. The finite cut-containment facts and four-cycle line
geometry belong here.

The already completed structural lemmas then supply:

- The concentrated opposite fourteen-failure classifications:
  four identical opposites with adjacent profile5,5, or three
  identical opposites with profile5,3,3; no variety can occur five
  times in a fourteen-failure.
- The mixed four-adjacent-class exclusion, when opposite varieties
  have multiplicity at most two.
- Pure fourteen-failure bounds: class cap three, at most eight
  occupied classes, at most five repeated classes, at most one
  own-loop triple, and a private column with an outsider matching
  for every nonloop triple.
- The no-own-loop pure fourteen-failure butterfly classification,
  the butterfly repeated-colour refinement, and the mixed one-
  opposite two-own-loop exclusion.
- The support-poset theorem and small common-corner and doubled-
  class constructions used in later local lemmas.

These are earlier hand results. Their proof statements do not assume
the new one-, two-, or three-opposite conclusions.

## 2. New local tools, independent of the final theorem

| Tool | File | Essential earlier dependencies |
| --- | --- | --- |
| Eleven capped adjacent sources sharing a corner assemble | `../three_opposite_double/common-corner-eleven-hand.md` | Common-corner3,2,2,2,1 and3,3,2,2-with-loop lemmas; explicit new completions |
| Adjacent profile3,2,2,2,2,1,1 assembles | `../elementary_alternative_next/five-repeated-classes-two-helpers.md` | Support-poset theorem, the five-doubled-class Hall criterion, and explicit helper matchings |
| Nine-source repeated-colour core | `../three_opposite_root/repeated-colour-closures.md`, Sections1–2 | Two own-loop triples and two displayed six-corner matchings |
| Compression of disjoint adjacent cuts | `../three_opposite_root/pair-compression-and-intersecting-cuts.md`, Section1 | Direct containment of an opposite variety's corners in two cuts |
| Three containing families for intersecting cuts | Same note, Section3 | The elementary star-or-triangle classification of intersecting edges |

The first three numerical tools do not use pair compression or the
full three-opposite theorem. Compression and family containment are
unconditional geometric statements; only their later numerical
application depends on the three-opposite theorem.

## 3. Independent numerical closures

### Pure fifteen cubes

`../root/pure-fifteen-elementary.md` uses the older pure fourteen
structure and deletion of triple copies. It is independent of every
mixed numerical theorem below. The same note supplies a directly
verified fourteen-cube obstruction for the eventual lower bound.

### One opposite and fourteen adjacent cubes

`../elementary_alternative_next/one-opposite-fourteen-adjacent.md`
is independent of the two- and three-opposite theorems. Its new
thirteen-source lemma excludes a sole-triple pure fourteen-failure.
A pure predecessor therefore has at least two triples. If it has
no own loop, use the earlier butterfly-plus-opposite construction.
Otherwise take a nonloop triple: the added opposite either meets
its private column and promotes a second loop, or avoids the whole
column and falls under one of three explicit private-column lemmas.

The root has already audited this joining logic and all its new
components. It does not require resolving the remaining pure
fourteen unique-own-loop classification.

### Four or more opposite cubes

The previous eight-, seven-, six-, five-, and four-opposite results
give the corresponding fifteen-source rows after the multiplicity
reductions in Section5 below. The four-opposite proof is indexed in
`../root/four-opposites-ten-adjacent.md`.

### Three opposite and eleven adjacent cubes

The adjacent class cap is three. Opposite profile1,1,1 is proved
in `three-distinct-eleven-adjacent.md`; all its components and its
joining argument have passed independent audits. Profile2,1 is
proved in the sibling's written chain
`../three_opposite_double/three-opposites-one-double-hand.md`;
its final path/joining review is the remaining review gate for
that profile at this checkpoint.

Three identical opposite sources are already covered by the old
concentrated fourteen-failure classification: adjacent profile5,3,3
would violate the cap three. Thus the two new profiles and that
older classification give the convenient uniform statement:

> Any three opposite sources and eleven adjacent sources of class
> multiplicity at most three assemble.

No opposite-variety cap is needed in this packaged version. The
fifteen-source row with three opposites follows by discarding one
adjacent cube.

## 4. Two opposite and thirteen adjacent cubes

This is the only new numerical closure that needs the three-opposite
fourteen-source theorem.

If two adjacent sources have disjoint tricoloured cuts, remove both
and introduce the one virtual opposite source from the compression
lemma. The resulting pool has three opposite and eleven adjacent
sources, so the uniform theorem in Section3 applies. Replace the
virtual source, if it was used, by an available one of the two
removed actual sources supplying its assigned corner. Source
distinctness is preserved.

If there is no disjoint adjacent pair, the support is contained in
one of three elementary families. Its numerical closures are:

| Family | Proof | Status at this checkpoint |
| --- | --- | --- |
| Two stars | `two-star-two-opposites.md` | Full independent root audit passed |
| Butterfly | `../elementary_alternative_next/butterfly-two-opposites-thirteen-adjacent.md` | Full independent audit passed; see `audit-butterfly-two-opposites.md` |
| Star and triangle | Sibling's current investigation | Final proof/audit still required |

The first two family proofs use no three-opposite theorem. Their
common-corner reductions and explicit source assignments are direct.
The star-and-triangle proof should likewise be checked for an
independent or strictly earlier dependency before this row is marked
complete. Once those gates are met, compression plus the three-family
containment proves the entire two-opposite fifteen-source row.

## 5. Joining the rows to obtain N5=15

Assume a fifteen-cube pool fails. The concentrated fourteen-failure
classifications first imply that every opposite variety occurs at
most twice. For four identical opposite cubes, deleting each of the
eleven adjacent cubes gives profile5,5 and hence9A=220, impossible.
For three identical opposites, the analogous deletion gives10A=192.
A fifth copy or a second opposite variety contradicts the same old
fourteen classifications directly.

Now the mixed concentration results imply that, whenever at least
one opposite cube occurs, every adjacent class has size at most
three: retain four of a class and an opposite source in a fourteen-
subpool to contradict the earlier mixed four-class exclusion. It
is important to establish the opposite cap first, because that is
a hypothesis of the mixed exclusion.

The remaining proof splits only by the number o of opposite cubes:

| o | Numerical theorem used |
| ---: | --- |
| 0 | Pure fifteen-source theorem |
| 1 | One-opposite fourteen-adjacent theorem |
| 2 | Compression plus the three pairwise-intersecting family closures |
| 3 | Three-opposite eleven-adjacent theorem after one adjacent deletion |
| 4 | Four-opposite ten-adjacent theorem after one adjacent deletion |
| 5 | Existing five-opposite constructions, splitting by the presence of an adjacent triple |
| 6 | Existing six-opposite constructions, splitting by the presence of an adjacent triple |
| 7 | Seven capped opposite sources and any adjacent source |
| at least8 | Eight capped opposite sources |

Every row contradicts failure once the gates identified above are
completed. This proves N5≤15. The independent fourteen-cube
obstruction in the pure theorem gives N5≥15, and hence equality.

## 6. Why there is no circularity

The two-opposite theorem is downstream of the three-opposite theorem
only through compression. The three-opposite theorem uses local
common-corner and repeated-colour constructions, not the two-opposite
conclusion. The one-opposite theorem uses the pure predecessor
structure and new private-column constructions, not compression or
the two-opposite result. The pure theorem uses neither mixed theorem.
All multiplicity reductions refer to earlier fourteen-source hand
classifications, not to N5=15.

The unresolved global fourteen-failure identity is outside this
dependency chain. In particular, proving the direct fifteen-source
rows need not settle fourteen-source pools with one or two opposite
cubes or the pure unique-own-loop branch.
