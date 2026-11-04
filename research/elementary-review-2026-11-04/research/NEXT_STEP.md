# Elementary-proof research: the fifteen-cube threshold is proved

4 November 2026

## Main outcome

**There is now a complete written elementary proof of N₅=15.**

Start with [fifteen-elementary-proof.md](root/fifteen-elementary-proof.md).
It states the model, proves the concentration reductions, joins all
opposite-count cases, gives an explicit fourteen-cube obstruction, and
records an acyclic dependency order. Every new branch and the final
joining argument have passed independent mathematical audits.

The argument uses Hall's theorem, small geometric case divisions,
explicit corner assignments, repeated-colour arguments, and elementary
counting. The full proof chain is substantial. Some lemmas retain
displayed finite Hall tables whose discovery and audit used computers;
the written tables and their completeness arguments are the proofs.
No exhaustive cube-inventory catalogue is a premise.

The direct proof bypasses the global identity 3A−4B=36 for fourteen
failures. That identity still has unresolved elementary branches.
No new Lean formalisation or kernel replay is claimed.

## 1. What closed in this round

| Result | Main proof note |
| --- | --- |
| Eleven adjacent cubes of class cap three sharing a tricoloured corner assemble. | [common-corner-eleven-hand.md](three_opposite_double/common-corner-eleven-hand.md) |
| Thirteen adjacent cubes with class profile (3,2,2,2,2,1,1) assemble. | [five-repeated-classes-two-helpers.md](elementary_alternative_next/five-repeated-classes-two-helpers.md) |
| Any one opposite cube and fourteen adjacent cubes assemble. | [one-opposite-fourteen-adjacent.md](elementary_alternative_next/one-opposite-fourteen-adjacent.md) |
| Any three opposite cubes and eleven adjacent cubes of class cap three assemble. | [three-opposites-eleven-adjacent.md](root/three-opposites-eleven-adjacent.md) |
| Any two opposite cubes and thirteen adjacent cubes of class cap three assemble. | [two-opposites-thirteen-adjacent.md](root/two-opposites-thirteen-adjacent.md) |
| O+3C(ac)+3C(bc)+2C(abc) assembles whenever O contains edge ab. | Sections 1–2 of [repeated-colour-closures.md](three_opposite_root/repeated-colour-closures.md) |

All statements count distinct physical sources. Adjacent-class
multiplicities refer to tricoloured-corner classes, not to individual
varieties. Repeated colours within those classes are unrestricted.
An assembly may have either target type unless a stronger conclusion
is explicitly stated.

### One opposite cube

Delete it to obtain a pure fourteen-failure. The new thirteen-source
lemma shows this predecessor cannot have only one triple class.
The established private-column structure and three new private-column
extension proofs then close the unique-own-loop branch. A predecessor
with no own loop was already handled by the butterfly extension.

The private-column notes are
`elementary_alternative_next/private-column-high-opposite.md`,
`private-column-diagonal-opposite.md`, and
`private-column-row-opposite.md` in the same directory. Their actual
dependencies are reviewed in
[audit-one-opposite-dependencies.md](elementary_alternative_next/audit-one-opposite-dependencies.md).

### Three opposite cubes

The three-distinct branch uses a common high target, a globally missing
edge lemma, a rectangle-family lemma, and a small Hall certificate for
the unique unsupported triad. The doubled branch reduces a Hall cover
to a missing bidirected edge or one of three directed-path forms.
The possible single variety is retained explicitly during symmetry
normalization. The three-identical branch is excluded by the earlier
elementary profile (5,3,3) and the adjacent class cap.

### Two opposite cubes

Two disjoint adjacent cuts jointly contain an opposite source's full
corner set. Replace one cube from each by that virtual source, apply
the three-opposite fourteen-source theorem, and restore a compatible
actual cube at the virtual source's assigned corner.

If no disjoint pair exists, signed pole pairs form two intersecting
edge families in K₅. Their support is contained in a butterfly, two
stars, or a star and triangle. All three numerical family lemmas are
now proved. The final star-and-triangle family reduces by two short
matching lemmas to the reversed nine-source construction above.

## 2. The shortened threshold proof

The old concentrated-opposite fourteen-failure classifications give
opposite-variety cap two in a hypothetical fifteen-failure. The two
deletion contradictions are 9A=220 and 10A=192. Mixed concentration
then gives adjacent-class cap three.

| Opposite total o | Result used |
| ---: | --- |
| 0 | Pure fifteen-cube theorem |
| 1 | One opposite plus fourteen adjacent cubes |
| 2 | Two opposite plus thirteen capped adjacent cubes |
| 3 or4 | Select three opposite and eleven adjacent cubes |
| 5 or6 | Select five opposite and nine adjacent cubes |
| 7 | Seven capped opposite cubes and any adjacent cube |
| At least8 | Eight capped opposite cubes |

The five-opposite/nine-adjacent theorem has been strengthened from
adjacent class cap two to three without changing its helper argument:
nine capped adjacent sources are either all in different classes, or
contain 2A+B+C for three different classes. The nine-source helper
lemma applies in the latter case.

The separate four-opposite/ten-adjacent and six-opposite/eight-adjacent
theorems remain valid stronger fourteen-source results, but are no
longer required in the shortest dependency chain for N₅=15.

The explicit lower-bound example is in Section 5 of the main proof.
Its six adjacent classes have multiplicities (3,3,3,3,1,1), with the
repeated colours displayed and every possible target excluded by hand.

## 3. Audit records and the role of computation

The final joining audit is
[audit-fifteen-elementary-master.md](three_opposite_double/audit-fifteen-elementary-master.md).
The uniform numerical joins and strengthened five-opposite statement
are separately reviewed in
[direct-threshold-joins-audit.md](root/direct-threshold-joins-audit.md).

Further explicit records include:

- [audit-root-replacement-and-nine-core.md](three_opposite_distinct/audit-root-replacement-and-nine-core.md);
- [audit-butterfly-two-opposites.md](three_opposite_distinct/audit-butterfly-two-opposites.md);
- [audit-doubled-path-components.md](elementary_alternative_next/audit-doubled-path-components.md);
- [audit-star-triangle.md](elementary_alternative_next/audit-star-triangle.md);
- [audit-one-opposite-dependencies.md](elementary_alternative_next/audit-one-opposite-dependencies.md).

The small checkers for fixed geometric tables and assignments are
retained alongside their results. Exploratory inventory searches,
failed stronger conjectures, and old checkpoints are also retained
as research history. They do not serve as unproved exhaustion steps
in the completed threshold argument.

For a fully local dependency bundle, the paper's eight-plus-three
common-missing-pair lemma is reproduced, with a direct cut-model
projection proof, in
[eight-plus-three-common-missing-pair.md](root/eight-plus-three-common-missing-pair.md).

## 4. Exact remaining scope of the fourteen-failure identity

For a fourteen-pool set A=Σ binom(g_j,2), B=binom(o,2).
The separate proposed identity is W=3A−4B=36 whenever the pool fails.

| Opposite total | Elementary status |
| ---: | --- |
| At least5 | No failures |
| 4 | Fully classified: four identical opposite sources and adjacent profile (5,5); W=36 |
| 3 | Fully classified: three identical opposite sources and adjacent profile (5,3,3); W=36 |
| 2 | Still need to exclude two opposite plus twelve capped adjacent sources; W=36 would require 3A=40, impossible |
| 1 | Still need to show a failing one-opposite/thirteen-adjacent pool has A=12, or exclude such failures |
| 0 | The no-own-loop branch is classified; the unique-own-loop fourteen-source branch remains for the identity |

The new thirteen-source lemma shows a pure fourteen-failure cannot
have just one triple class. It does not by itself classify the
unique-own-loop branch. None of these three open identity branches
is a hypothesis of the direct fifteen-cube proof.

## 5. Publication and provenance

The mathematical gap for an elementary proof of the threshold is
closed. The remaining work for presenting this proof in the paper
is consolidation and substantial shortening: standardize the
notation, reduce duplicated Hall arguments, isolate reusable local
constructions, and decide which fixed tables belong in an appendix.

The production repository at commit
`1dce44d24f76e84f0266025ab9ce0ab94a306873` was not modified.
These are reviewable research proofs and diagnostic files. The
previous global checkpoint is preserved in
`history/2026-11-03-four-opposite-checkpoint.md`; its open-case
statements are historical and are superseded by this document.
