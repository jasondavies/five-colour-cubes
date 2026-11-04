# One opposite cube and fourteen adjacent cubes

4 November 2026

**Status: elementary proof; independent root audits of the joining
logic, thirteen-source lemma and three private-column lemmas passed.**

## Theorem

Any pool consisting of one opposite-repeat five-colour cube and
fourteen adjacent-repeat five-colour cubes contains eight cubes
assembling a five-colour 2×2×2 cube with monochromatic faces.

There is no multiplicity assumption in the statement. The necessary
class bounds arise from the already proved pure fourteen-cube theory.
The proof does not assume the fourteen-failure catalogue or the
general N5=15 theorem.

## 1. Elementary facts about a pure fourteen-failure

The previous structural work proves that every failing pool of
fourteen adjacent cubes has the following properties:

1. Every adjacent tricoloured-corner class has count at most three.
2. At most eight classes occur, and at most five classes occur twice
   or more.
3. At most one triple class has an own-orientation loop: a matching
   of its six tricoloured corners after two of its cubes are reserved.
4. Every triple without such a loop has exactly two private corners,
   forming one column of its two-by-three corner array. Its other
   four corners have an outsider matching.
5. If no triple has an own loop, the pool has butterfly support.

The dependency references are `../root/pure-fifteen-elementary.md`,
`../pure_supported/two-own-loop-triples-hand.md`,
`../pure_supported/private-row-unconditional-hand.md`,
`../pure_supported/private-diagonal-unconditional-hand.md`,
`../pure_supported/private-pair-promotion-hand.md`, and
`../root/g3-private-column-hand.md`.

The thirteen-source theorem
`five-repeated-classes-two-helpers.md` now adds:

6. A pure fourteen-failure has at least two triple classes.

Indeed a pure failure has at least one triple by the previous
concentration and diversity results. If it has exactly one, properties
1 and2 force its counts to be3,2,2,2,2,1,1,1. The new theorem solves
the subpool retaining two of its singleton classes.

## 2. Add the opposite cube

Let P be the fourteen adjacent cubes and O the opposite cube.
Suppose P+O fails. Then P is itself a pure fourteen-failure.

If P has no own-loop triple, property5 places it in the butterfly
family. The earlier elementary lemma
`../mixed_diffuse/butterfly-plus-opposite-hand-proof.md` says that
any opposite cube added to such a failure gives an assembly.
This case is therefore impossible.

Otherwise P has precisely one own-loop triple U. By property6 there
is another triple A, which has no own loop. Property4 gives A a
private column and an outsider matching of its other four corners.

If O contains one of A's two private corners, reserve two A cubes,
put O at that private corner, use the remaining A at the other one,
and use the four outsider matches at the other four corners. Thus
A gains an own loop in P+O. The loop on U persists. The elementary
mixed two-own-loop theorem
`../mixed_diffuse/two-own-loop-triples-one-opposite-hand.md`
excludes two such triples in a failing fifteen-pool with one
opposite source. Hence this case also assembles.

It remains that O avoids A's whole private column. Normalize A to
C(01) and the column to02,12. The eleven adjacent outsiders all
avoid those two corners by privacy. They have class cap three by
property1. An opposite variety avoiding02,12 has one of exactly
five forms, falling into three geometric types:

| Type | Representative edge set | Elementary proof |
| --- | --- | --- |
| High | {03,04,13,14} | `private-column-high-opposite.md` |
| Diagonal | {01,04,13,34} | `private-column-diagonal-opposite.md` |
| Row | {13,14,23,24} | `private-column-row-opposite.md` |

Those three notes prove that three A sources, the eleven capped
adjacent outsiders and O always assemble. Their proofs use small
Hall tests and explicit source allocations; the high and diagonal
types finish with intersecting own-loop triples.

This excludes the last possibility. Therefore every pool of one
opposite and fourteen adjacent cubes assembles, as claimed.

## Scope and independence

The proof closes the one-opposite row of the direct fifteen-cube
problem. It does not classify fourteen-cube failures with one
opposite source, and it does not finish the pure fourteen unique-
own-loop classification needed for the global invariant identity.

The new thirteen-source lemma uses the older support-poset theorem,
the explicit three-from-one-side constructions from the six-doubled-
classes proof, and the common-corner3,2,2,2,1 lemma. None depends on
the one-opposite conclusion. The private-column arguments use only
cut incidence, Hall's theorem, and direct repeated-colour counting.
The dependency chain is acyclic.

The precise dependency trace is recorded in
`audit-one-opposite-dependencies.md`. In particular the pure-fifteen
synthesis note cited as a guide above is not itself a theorem used
in this proof; its earlier component lemmas supply properties1–5.

No new Lean formalisation is claimed, and the production repository
has not been modified.
