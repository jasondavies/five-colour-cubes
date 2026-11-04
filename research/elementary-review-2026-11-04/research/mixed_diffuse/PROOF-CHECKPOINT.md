# Mixed diffuse branch: checkpoint after the one-opposite proofs

**Update, 4 November 2026.** The local concentration proofs indexed
below are inputs to the now-complete direct elementary proof of
N₅=15 in `../root/fifteen-elementary-proof.md`. In particular, the
one-opposite/fourteen-adjacent theorem is proved in
`../elementary_alternative_next/one-opposite-fourteen-adjacent.md`:
the sole-triple predecessor and private-column avoidance gaps described
below have both been closed. See `../NEXT_STEP.md` for current status.

**The remainder is a historical checkpoint.** Its local hand proofs
remain valid; its descriptions of global or one-opposite gaps are
superseded by the current proof.

All files below are research notes. The production repository was not
edited. “Diffuse” means every opposite variety has multiplicity at most
two. Write m for the total opposite-source count and g for an adjacent
tricoloured-corner class count.

## Established hand proofs

| Statement | Proof file | Main dependencies |
|---|---|---|
| Five copies of one adjacent class solve a mixed diffuse fourteen-pool | `five-class-mixed-hand-proof.md` | Existing six-class lemma; shared-four bound; elementary rectangle matchings |
| Four copies of one adjacent class solve when m≥4 | `four-class-four-opposites-hand-proof.md` | Same-repeat pair; seven three-corner geometries; two small corner tables |
| Four copies solve when m=3 | `four-class-three-opposites-hand-proof.md` | Five-class note's thirteen-cube corollary and disjoint-source cores; direct rectangle constructions |
| Four copies solve when m=2 and the opposite varieties differ | `four-class-two-distinct-opposites-hand-proof.md` | Thirteen-cube corollary; shared-four bound; direct rectangle constructions |
| Four copies solve when m=2 and both opposite sources are identical | `four-class-two-identical-opposites-hand-proof.md` | Earlier concentration bounds; thirteen-cube corollary; one explicit repeated-colour triangle |
| Four copies solve when m=1 | `four-class-one-opposite-hand-proof.md` | Two-corner transfer from the existing pure five-class proof; row-cover path lemma; direct rectangle and colour-triangle constructions |
| The row-triple cover in the m=1 case solves | `one-opposite-row-cover-hand-proof.md` | Six-position path Hall argument; shared-four bound; two explicit repeated-colour triangles |

The five-class note supplies five useful eight-cube cores. Here Z means
an adjacent source whose tricoloured corners are disjoint from A:

    4A + 3Z + O;
    3A + 3Z + 2O;
    3A + 4Z + O;
    4A + 2Z + two distinct O;
    3A + 2Z + three diffuse O.

The first three allow repeated opposite varieties without restriction.
The last two have the indicated distinctness/multiplicity requirements.
It also proves the nine-piece lemma

    5A + two distinct O + any two other sources solve.

Sections 5–6 of that note use only four A in their final constructions.
This yields its explicit thirteen-cube corollary: four A, t identical O
(t=1 or2), and9−t adjacent sources whose A intersections all lie in the
pair O∩A solve, under the class and shared-four bounds.

## Exact cumulative consequence

For a putative mixed diffuse fourteen-cube failure:

* For every m≥1, every adjacent class has size at most three.
* If m≥3, every adjacent class of size three has disjoint-adjacent
  mass at most one.
* For m=2, a three-copy class has disjoint-adjacent mass at most two.
* For m=1, a three-copy class has disjoint-adjacent mass at most three.

These conclusions are elementary and do **not** depend on the finite
eight-cube lemma that conditionally reduces m to at most four.

## Audits and proof status

Every displayed explicit matching in the seven hand-proof files was
checked against the directed cut/biclique model. The script
`audit_hand_notes.py` independently checks all five local core families,
all290 two-helper cases in the seven four-opposite geometries, and the
three permutations of the repeated-colour triangle profile3,3,2.
Its output is `hand-notes-audit.json`.

The additional script `audit_one_opposite_notes.py` checks the new
one-opposite reductions independently. It verifies all16,494 coarse
vectors in the five three-corner cover shapes under the class,
shared-four and disjoint-mass bounds; no missing-pair bound is used.
It also checks1,222 six-variable path vectors and the three new
repeated-colour triangles. All checks passed. The output is
`one-opposite-hand-proof-audit.json`.

The prose arguments are complete for their stated branches. No known
gap remains in those written arguments. The audit is a check on them,
not a substitute for any missing case in the proofs.

## Explicitly unresolved here

The general mixed branch with all g≤3 remains unproved here. This
checkpoint makes no claim to the full identity3A−4B=36 or the complete
elementary N5 proof.

The three-corner reduction for m=1,g=4 has been exhaustively audited at
the coarse level, subject to the class, disjoint-mass, shared-four and
missing-pair bounds. `g4-three-cover-O1.json` records32 opposite-unsolved
coarse vectors over the chosen normalizations:24 in the row shape and8
in a diagonal column-pair shape. Each is eliminated by a loop at a
four-copy class or a two-class repeated-colour clique. This older
computational classification has now been replaced by the complete
hand arguments in the two one-opposite proof notes.

Likewise `double-low-O3.json` and `double-low-O4.json` audit Hall covers
of sizes3–5 at a doubled opposite anchor under g≤3 and the new
disjoint-mass cap. They leave30 and8 labelled coarse opposite-unsolved
vectors respectively, all with two-class repeated-colour clique
obstructions. Their classification remains computational.

The older O2 three-corner audit has been superseded, for its mathematical
conclusion, by the written hand proofs above.

## Completed one-opposite path argument

For the row cover H={02,03,04}, with O=opposite04|23 and no sources
disjoint from A, the nine helpers belong to

    F2=C(02), F3=C(03), F4=C(04),
    G2=C(034), G3=C(024), G4=C(023).

For the opposite target14|23 (omitting0), two A fill12,13. On the
remaining positions ordered as24,21,43,42,31,34, the helper
neighbourhoods F2,G3,F4,G2,F3 are the five consecutive edges of a
six-vertex path; G4 sees its outer four positions, and O sees its
two ends and two central positions.

The companion note now proves the Hall classification into the three
support families {Fi,Fj,Gk}, with {i,j,k}={2,3,4}. Hall sets of size
at least three are controlled by the class and shared-four bounds;
the singleton/pair conditions give those families and one further
family that has an explicit opposite assembly. Each surviving family
then forces counts3,3,3 in a looped, pairwise conflicting triangle.

The full one-opposite proof also records the two-corner transfer from
Sections3–5 of `research/root/pure-five-class-hand.md`. The parent
agent independently audited that transfer: every construction uses
at most four A except two A–singleton-class conflicts, in which the
opposite source at an A corner outside the cover replaces the fifth A.

## Further hand results for fifteen cubes

Three subsequent notes are complete for their stated hypotheses:

| Statement | Proof file | Dependencies |
|---|---|---|
| Adding any opposite cube to a failing butterfly fourteen-pool solves | `butterfly-plus-opposite-hand-proof.md` | The elementary butterfly refinement classification; explicit eight-cube assignments |
| A failing fifteen-pool with exactly one opposite cube and adjacent class cap three has at most one own-loop triple | `two-own-loop-triples-one-opposite-hand.md` | Universal restoration; the eight-cube core `3A+4Z+O`; explicit nested-cut assignments |
| Four common-corner classes of counts `3,3,2,2` solve if either triple has an own loop in the full pool | `common-corner-3322-own-loop-hand.md` | Three elementary support geometries; explicit conflict matchings and repeated-colour arguments |

The mixed two-own-loop theorem permits the opposite cube in either
asserted own-loop matching. The only delicate transfer from the pure
two-own-loop theorem is handled directly: eight adjacent helpers
cannot all belong to the main classes, because one main block has
capacity six and two present main blocks have capacity four. Thus
the necessary outer source exists without assuming that an anchor
loop avoids the opposite cube.

The common-corner proof does not classify weight vectors by search.
The two absent classes are either in one family, a matched pair, or
an unmatched pair. Those are its three support cases. Its explicit
assignments and all 36 normalized choices of weight placement and
asserted triple loop were independently checked by
`audit_common_corner_3322.py`; the report is
`common-corner-3322-own-loop-audit.json`. The butterfly note has an
independent 135-case audit in `butterfly-plus-opposite-audit.json`.
The parent independently audited both the mixed two-own-loop note
and the common-corner `3,3,2,2` note, including the opposite-sensitive
steps, all clique assignments, and the forced-repeat case. No gap
was found.

The common-corner lemma combines with the sibling's elementary
`../pure_supported/common-corner-32221-hand.md` to close the final
capacity exceptions in the private-row argument. The sibling is
writing the complete unconditional private-row extension separately.
Once that extension is established, every non-own-loop triple in a
pure fourteen-failure has exactly two private corners: it has at
least two by the nonprivate-triple theorem, while three private
corners would contain a private row pair.

## Exact remaining one-opposite fifteen-cube gap

Delete the opposite cube from a hypothetical failing fifteen-pool.
The predecessor is a failing pure fourteen-pool. If it has no
own-loop triple, the proved private-column theorem classifies it as
a butterfly, and the first new note above solves the extension.

Otherwise the predecessor has a unique own-loop triple. The
private-pair promotion lemma in
`../pure_supported/private-pair-promotion-hand.md`, together with
the mixed two-own-loop theorem, shows the following:

> A failing extension's opposite cube avoids both private corners
> of every other triple having exactly two private corners.

The missing hand argument is to exclude such avoidance. In
particular, the present notes do not yet prove that a predecessor
with a unique own-loop triple must have another triple; an absence
of other triples would make the avoidance condition vacuous.

The new discovery sweep `private_pair_opposite_sweep.cpp` examines
the conditional branch with a specified nonloop triple, class cap
three, at most eight occupied classes, at most five repeated
classes, exactly one own-loop triple, and every other triple having
exactly two private corners with no private row pair. Its output is
explicitly diagnostic, not a proof:

* With a normalized private column `{02,12}`, it leaves 120 labelled
  pure coarse profiles without an opposite assembly. An opposite
  source avoiding all the nonloop triples' private pairs occurs in
  144 profile/source instances: 66 each for types 60 and 63, and
  12 for type 66. Every one gives an opposite assembly after the
  added cube is included.
* With a normalized private diagonal `{02,13}`, it leaves no pure
  coarse profile without an opposite assembly.

The two outputs are `private-column-opposite-discovery.jsonl` and
`private-diagonal-opposite-discovery.jsonl`. Neither is used in a
hand theorem. A structural proof of the diagonal exclusion and of
the column avoidance result would remove these remaining conditional
cases; existence of a nonloop triple would still need justification
unless supplied by another argument.

No production file was modified, and no complete elementary proof
of the unrestricted mixed fifteen-cube theorem or the global
fourteen-failure identity is asserted in this checkpoint.
