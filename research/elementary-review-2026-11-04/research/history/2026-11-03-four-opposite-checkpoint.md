# Elementary-proof research: current checkpoint

3 November 2026

## Main outcome

The latest round closes the next target:

> **Four-opposite theorem.** Four opposite sources with variety cap
> two and ten adjacent sources with class cap three contain eight
> cubes assembling a five-colour target with monochromatic faces.

The proof chain is collected in `root/four-opposites-ten-adjacent.md`.
All three opposite multiplicity profiles are closed. The last branch
uses repeated colours to construct an adjacent target; the theorem
does not assert that an opposite target always works. Each component
argument and the final joining lemma passed independent audit.

The preceding round proved the five-opposite theorem: five capped
opposite sources plus 2A+B+C suffice for three distinct adjacent
classes A,B,C. See `root/five-opposites-nine-adjacent.md`.

The earlier round also established:

> **Pure adjacent theorem.** Any fifteen adjacent-repeat five-colour
> cubes contain eight that assemble a five-colour 2×2×2 cube with
> monochromatic faces. Fourteen do not suffice.

> **Eight opposite theorem.** Any eight opposite-repeat five-colour
> cubes, with each variety occurring at most twice, assemble an
> opposite-repeat target using all eight cubes.

It also closes the six-opposite case, the seven-opposite case, and the
last mixed fourteen-cube case containing four cubes in one adjacent
tricoloured-corner class.

**The full elementary proof of N₅=15 and the identity 3A−4B=36 for
every fourteen-cube failure remain open.** The exact remaining cases
are listed below. These notes do not replace the established
computer-assisted proof in the paper, and no new Lean formalisation
has been made.

Start with `root/four-opposites-ten-adjacent.md`,
`root/five-opposites-nine-adjacent.md`,
`root/pure-fifteen-elementary.md`,
`root/eight-opposite-elementary.md`, and
`root/fifteen-case-reduction.md`. The older `FOLLOWUP.md` and the
historical material in `README-elementary.md` describe earlier stages;
their lists of open cases are superseded by this checkpoint.

## Definitions

A five-colour cube uses five colours on its six faces. Its repeated
colour occurs on either adjacent or opposite faces. Cubes can be
properly rotated independently.

An adjacent tricoloured-corner class consists of the three varieties
having the same six oriented tricoloured corners. In the directed-cut
model, these are C(S)=S→Sᶜ, where |S| is two or three. There are twenty
classes. The class count g_j is a count of physical cubes, potentially
of different varieties within the class. An opposite variety is an
undirected four-cycle of K₅; each edge supplies both directed corners.

A pool fails if no eight distinct physical cubes can match all eight
corners of any five-colour target. Write o for its total number of
opposite sources, A=Σ_j binom(g_j,2), B=binom(o,2), and W=3A−4B.

Call a triple class *own-looped* when, after reserving two of its cubes,
the remaining pool can match all six of that class's tricoloured
corners. This is only a tricoloured-corner condition: the two reserved
cubes need not match the same target's bicoloured corners. It is
monotone under adding cubes.

## 1. A complete elementary proof for fifteen adjacent cubes

Three structural facts suffice for a short deletion argument.

1. A failing pure fourteen-pool has class counts at most three. Nine
   occupied classes already give an assembly, as do six repeated
   classes in a fourteen-pool.
2. A pure fourteen-failure with no own-looped triple has the butterfly
   profile 3,3,3,3,1,1.
3. A failing pure fifteen-pool with class counts at most three cannot
   have two own-looped triples.

The new result in (2) is the column-private classification in
`root/g3-private-column-hand.md`. The proof of (3), including its
fifteen-cube extension, is in
`pure_supported/two-own-loop-triples-hand.md`.

Suppose a pure fifteen-pool fails. Every fourteen-subpool fails, so
all class counts are at most three. At most eight classes occur. If
all counts were at most two, there would be seven doubled classes;
a fourteen-subpool retaining six of them would assemble. Thus some
class T is a triple.

Delete one cube of T. The resulting fourteen-failure has a doubled
class, so it cannot have profile 3,3,3,3,1,1. It therefore has an
own-looped triple U, necessarily different from T. This property
persists when the deleted cube is restored. Repeat the deletion
argument with T=U. It produces a second own-looped triple, contradicting
(3).

This bypasses the remaining classification of pure fourteen-failures
with a unique own-looped triple. The proof chain is elementary but
longer than the final deletion argument alone.

An explicit fourteen-cube obstruction and its hand verification appear
in `root/pure-fifteen-elementary.md`, establishing sharpness.

## 2. Private corners in all pure fourteen-failures

The private-column conclusion now holds even when another triple is
own-looped:

> Every non-own-looped triple in a pure fourteen-failure has exactly
> two private corners, forming a column of its 2×3 corner rectangle.
> Its four other corners can be matched by four outside cubes.

The main notes are:

- `pure_supported/private-row-unconditional-hand.md`;
- `pure_supported/private-diagonal-unconditional-hand.md`;
- `pure_supported/private-pair-promotion-hand.md`.

These use two independently useful common-corner results. A
3,2,2,2,1 core in five of the six classes through one directed corner
always assembles. A 3,3,2,2 core does so if either triple is own-looped
in the full pool. See `pure_supported/common-corner-32221-hand.md`
and `mixed_diffuse/common-corner-3322-own-loop-hand.md`.

The promotion consequence is particularly useful: adding a source
meeting either private corner creates an own loop. Reserve two cubes
of the triple, use its third cube at the other private corner, and
use four outsiders at the other four corners.

The first draft of the diagonal proof confused row and column pairs
for negative cuts. That draft was replaced; the current version
handles the orientation explicitly and has passed independent audit.
Discovery data are retained as discovery data, not as proof inputs.

## 3. Eight opposite cubes, and seven plus any adjacent cube

The eight-opposite proof is a short finite-geometric case analysis on
the number of doubled varieties. Its basic construction is the five
distinct opposite varieties avoiding two specified edges of K₅.
These five sources fill any five corners of a suitable central target.
There are only two geometric forms, according as the forbidden edges
meet or are disjoint; both are displayed explicitly in the proof.

Eight distinct varieties, or one doubled variety, are settled by this
five-source construction and Hall's theorem. Three doubled varieties
are covered by the earlier three-pairs construction. Two doubled
varieties sharing two edges are covered by the neighbouring-pairs
construction. The remaining two-double case, where the varieties
share one edge, reduces to a companion variety or to the three
four-cycles inside K₄ or K₂,₃. All matchings and inequalities are
written in `root/eight-opposite-elementary.md`.

There is a useful stronger mixed consequence:

> Seven opposite sources, with variety multiplicities at most two,
> together with any adjacent source assemble using all eight cubes.

Temporarily replace the adjacent cube by a compatible opposite
variety whose multiplicity is less than two. Apply the eight-opposite
theorem. If the corner assigned to the temporary cube has the wrong
direction for the adjacent cube, reverse every directed corner of
the matching. This preserves the opposite target and all seven
actual opposite sources, and makes the replacement compatible. If
all three possible temporary varieties are doubled, the three-pairs
construction applies directly.

This also proves that the graph of possible single holes left by
seven opposite sources has a connected component on at least four
vertices. That fact drives the six-opposite argument.

## 4. Six opposite cubes plus eight adjacent cubes

The following fourteen-cube case is now closed:

> Six opposite sources with variety multiplicities at most two,
> together with eight adjacent sources whose class multiplicities
> are at most two, always assemble.

See `opposite_small_lemma/six-opposites-eight-adjacent.md`.

For a fixed target, the pairs of corners that can remain uncovered
after matching six opposite cubes are the bases of a rank-two dual
transversal matroid. Equivalently, the eligible holes divide into
parallel classes, and exactly the pairs from different classes can
be left empty together. If H is the union of eligible hole positions,
then |N_O(H)|=|H|−2, by alternating-path reachability.

If the adjacent cubes can reach two different parallel classes, two
distinct adjacent cubes complete the target. If they cannot, their
collective avoidance of the other classes is very restrictive:
eight adjacent sources with class cap two cannot have seven sources
all avoiding two undirected edges.

Adjoining a temporary seventh opposite source and applying the
seven-source hole-graph theorem reduces the only surviving geometry
to a three-edge path. Contracting its exceptional edge leaves two
cases. Each forces four doubled adjacent classes, and the note gives
an explicit eight-cube assembly in both cases.

Together with the earlier six-opposite/triple-class construction,
this solves every remaining six-opposite case in both the fourteen-
and fifteen-cube routes.

## 5. Mixed concentration and the one-opposite residual

The formerly open mixed case with exactly one opposite cube and an
adjacent class of size four is now solved. The proof is in
`mixed_diffuse/four-class-one-opposite-hand-proof.md`, with its
supporting row-cover lemma in
`mixed_diffuse/one-opposite-row-cover-hand-proof.md`.

Consequently every residual mixed fourteen- or fifteen-failure has
adjacent class sizes at most three. With five opposite sources, the
earlier triple-class construction strengthens this bound to two.

For fifteen cubes with exactly one opposite source, delete that source.
If the fourteen adjacent cubes have no own-looped triple, they form a
butterfly failure. Any opposite cube completes such a failure, by
`mixed_diffuse/butterfly-plus-opposite-hand-proof.md`.

Thus an unresolved one-opposite fifteen-failure must have a pure
fourteen predecessor with a unique own-looped triple. The added
opposite cube must avoid every other triple's private column: meeting
one would promote it to a second own-looped triple, and the mixed
two-own-loop theorem would give an assembly.

This avoidance case is open. We have also not proved that the pure
predecessor must have another triple. An argument using the other
triples must either prove their existence or cover the case without
them.

## 6. Closing the five-opposite target

The new replacement lemma says that if five opposite cubes plus 3A
assemble an opposite target, then the same five plus 2A+B assemble
for any adjacent source B. The three A corners occupy three distinct
underlying target edges, while B meets at least two. Choose a common
edge and replace that A. If its direction is wrong, swap the two
directions on that one edge; the other occupant is an opposite cube
and remains compatible. The other A assignments are unchanged.

If the temporary 3A pool fails, the old five-opposite grid cover
applies. Every final construction uses exactly two actual A cubes
and one helper meeting a rescue set. At most two adjacent classes
avoid this set, including A. Thus two other distinct helper classes
B,C cannot both fail. The neighbouring-pair case already accepts
any B different from A.

This proves the nine-source statement O+2A+B+C. To apply it to
five opposite and nine capped adjacent cubes, choose a doubled class
A and two other classes if a double occurs. If all nine classes are
distinct, the earlier nine-class theorem applies directly.

Combined with the earlier concentration results, every fourteen-cube
pool containing at least five opposite cubes now assembles, without
multiplicity assumptions. The corresponding fifteen-cube cases
therefore also assemble.

A stronger eight-source theorem O+2A+B, A≠B, has separately been
proved for opposite profile 2,2,1. Its four exceptional matchings are
in `five_opposite_profiles/two-pairs-two-adjacent-one.md`. The uniform
nine-source proof is sufficient for the present target.

## 7. Closing the four-opposite target

There are exactly three multiplicity profiles under the opposite
variety cap two: 1,1,1,1; 2,1,1; and 2,2.

- For four distinct varieties, the rank-two hole geometry of a
  repeated adjacent class reduces to two central-target configurations.
  Each admits a four-corner adjacent matching whose complement is
  filled by the four opposite cubes.
- With one doubled variety, the three varieties have a common target
  on which each meets at least two edges. A fully supported target
  gives a Hall completion, using a separate globally adjacent-zero-edge
  lemma if needed. The remaining geometry has one unsupported edge
  and exactly two marked forms; both have explicit helper proofs.
- With two doubled neighbouring varieties, any four distinct adjacent
  classes suffice. For nonneighbours, the missing edges form a path.
  Failure forces one avoided direction on each path edge. The three
  orientation types reduce the remaining adjacent counts to three
  triples and a singleton. A repeated-colour argument assembles the
  final family, already using an eleven-cube core.

The detailed proof and dependencies are in
`root/four-opposites-ten-adjacent.md`. This is a hand proof using
small geometric classifications; diagnostic inventory searches are
not premises.

Consequently every fourteen-failure with exactly four opposite cubes
has four copies of one variety and adjacent class sizes 5,5, by the
earlier concentrated classification. Its invariant is W=36. These
concentrated fourteen-failures do exist, so the conclusion is not
that every pool with four opposite cubes assembles.

Every fifteen-pool with at least four opposite cubes is now covered:
the previous deletion argument excludes concentrated opposite
varieties, and with variety cap two and adjacent class cap three,
retain four opposite and ten adjacent cubes and apply the new theorem.

## 8. Exact remaining scope

For a direct elementary proof with fifteen cubes, every hypothetical
failure now satisfies:

| Opposite total o | Opposite variety cap | Adjacent class cap |
| ---: | ---: | ---: |
| 1,2,3 | 2 | 3 |

The cap on opposite varieties follows from the earlier elementary
fourteen-failure classifications, not from the computer catalogue.
If a fifteen-failure has four copies of one opposite variety, it has
eleven adjacent sources. Deleting each adjacent source gives profile
5,5, and counting surviving adjacent pairs yields 9A=220, impossible.
For three opposite copies, the profile is 5,3,3 and the same argument
gives 10A=192, also impossible. A second opposite variety or five
copies of one variety is already excluded by the fourteen-classification.

The all-adjacent case and every o≥4 case are solved. See
`root/fifteen-case-reduction.md` for the complete deduction.

For the original fourteen-failure identity strategy, the remaining
mixed totals and caps are the same, but there is one fewer adjacent
cube. In addition, the pure fourteen case with a unique own-looped
triple still needs classification. Proving only the direct-fifteen
table would establish N₅=15 elementarily without requiring that
extra fourteen-failure classification or the global W identity.

A focused next mixed target is three opposite cubes plus eleven adjacent
cubes, with opposite variety cap two and adjacent class cap three.
This would close the largest remaining opposite total for both routes.
The weaker three-plus-twelve statement would suffice for the direct
fifteen-cube route alone.

## 9. Verification and provenance

The hand arguments above were audited independently. Finite checks
were also run to detect incorrect incidence claims or assignments;
they are corroboration, not substitutes for the written proofs.

- The four-opposite proof has audited component notes for the three
  multiplicity profiles. The last common-high-target kernel audit is
  in `four_opposite_root/common-high-audit.md`. Small geometric
  matchings, path cut tables, and the explicit endpoint and alternating
  constructions were also checked independently. The proof chain is
  indexed in `root/four-opposites-ten-adjacent.md`.
- The five-opposite target and the nine-source helper lemma passed a
  separate full mathematical audit, in
  `five_opposite_computation/five-target-proof-audit.md`. Its geometric
  checker verifies the grid and line forms, 46 rescue sets, and 370
  helper assignments; no fourteen-cube inventory search is used.
- `five_opposite_holes/check_low_repetition_geometry.py` independently
  checks the low-repetition grid reduction and its central-target
  completions. All 8,463 normalized inventories pass; the written
  proof uses only the two grid shapes and the line geometry.
- `five_opposite_profiles/audit_two_pairs.py` checks the four extra
  matchings for the stronger eight-source 2,2,1 lemma and its exact
  avoiding-class assertions. All passed.

- `python3 research/root/verify_next_step.py` checks the column
  geometry, small Hall-cover patterns, displayed assignments,
  fourteen-cube obstruction, opposite-source constructions, and the
  final six-opposite path cases. It passed.
- `research/root/check_eight_opposite.cpp` independently constructs
  the fifteen opposite varieties and checks all 157,950 inventories
  of eight sources with cap two. It found zero exceptions. Counts
  by number of doubled varieties were 6,435; 45,045; 75,075; 30,030;
  and 1,365. Results are in `root/eight-opposite-audit.json`.
- The mixed-agent audits check 16,494 coarse cover vectors and 1,222
  path count vectors, the common-corner assignments, and all
  9×15=135 butterfly-refinement/opposite-source combinations.
- The pure common-corner audit checks 76 explicit witnesses across
  all twenty normalized placements of the triple and singleton.

The production repository at commit
`1dce44d24f76e84f0266025ab9ce0ab94a306873` was not modified. These are
research notes and reproducible checks for review, not a claim of a
new machine-checked theorem or a completed elementary replacement
for the paper's full proof.
