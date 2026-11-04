# Independence audit of the one-opposite fifteen-cube route

4 November 2026

**Outcome: PASS.** The proof in `one-opposite-fourteen-adjacent.md`
has an acyclic dependency chain of elementary matching and
repeated-colour arguments. It does not assume N5=15, the pure
fifteen-cube theorem, the fourteen-failure inventory, or the proposed
global identity3A−4B=36.

The audit traces the exact lemmas used, rather than treating a whole
research folder or an exploratory checkpoint as a premise.

## 1. Foundations and pure fourteen-cube bounds

All branches use the directed-cut model, Hall/König matching,
pigeonhole on the three repeats permitted by a pole pair, and
explicit source assignments. The universal-restoration observation
is a local matching operation: it has no numerical threshold premise.

The pure fourteen bounds enter in this order:

| Required fact | Actual elementary source | Dependency check |
| --- | --- | --- |
| Class multiplicity at most five | `../root/six-adjacent-elementary.md` | Self-contained source allocations and Hall arguments for fourteen cubes; no global solvability theorem. |
| Class multiplicity at most four | `../root/pure-five-class-hand.md` | Uses the preceding concentration bound, a half-array construction, small Hall covers and repeat counting. |
| Class multiplicity at most three | `../pure_supported/g4-row-hand.md`, `g4-hook-disjoint-hand.md`, `g4-exception-hand.md` | Direct four-anchor Hall-cover proofs. The hook proof uses the earlier row core; the exception proof uses both earlier cover proofs. No triple-private theorem is used. |
| At most eight occupied classes | `../root/nine-distinct-hall-proof.md` | Six five-edge graph cores and displayed finite Hall tables. No fourteen-source inventory is enumerated or invoked. |
| At most five repeated classes | Corollary of `../root/six-doubled-classes-hand.md` | Uses its direct doubled-source constructions, the independent support-poset reduction, and the conditional butterfly profile proof. |

The support-poset reduction in Section0 of
`../support_families/elementary-support-family-proofs.md` is a
five-point partial-order argument. Its conditional butterfly profile
proof starts from the six-copy concentration bound and direct robust
matchings. It does not assume that all pure failures have butterfly
support. Consequently using that profile in the six-repeated-class
corollary is not circular.

These bounds already force a triple in a pure fourteen-failure:
fourteen sources in at most eight classes of cap two would have
at least six doubled classes. No fifteen-cube theorem is needed.

## 2. Own loops and private columns

The pure at-most-one-own-loop-triple theorem is Sections1–3 of
`../pure_supported/two-own-loop-triples-hand.md`. Its proof is
direct repeat-set exclusion, a disjoint/nested pole-pair split,
and explicit assignments. Its later pure-fifteen extension is not
used in the one-opposite route.

The private-column theorem has the following earlier dependencies:

1. `g3-nonprivate-hand.md` uses the already proved four-anchor
   matching constructions, with an exceptional source replacing
   the fourth anchor. It gives at least two private corners to
   every non-own-loop triple.
2. `private-row-unconditional-hand.md` uses that result, the pure
   two-own-loop exclusion, six-repeated-class bound, and the local
   common-corner lemmas for nine sources,3,2,2,2,1, and3,3,2,2
   with a looped triple. The latter lemma happens to be stored in
   `mixed_diffuse/`, but is proved entirely by local completions;
   it does not assume the one-opposite result. The row proof borrows
   only the portions of the older conditional row proof that do not
   assume privacy of the other triples.
3. `private-diagonal-unconditional-hand.md` then excludes diagonal
   pairs using the row lemma, the nonprivate lemma, the pure loop
   exclusion, and rectangle matchings. This order is acyclic.
4. `private-pair-promotion-hand.md` gives an outsider matching of
   the four nonprivate corners and hence promotion by any added
   source meeting a private corner. It has its own Hall and repeat
   argument; it does not assume the one-opposite conclusion.

If no triple is own-looped, the older conditional row/diagonal
proofs and `../root/g3-private-column-hand.md` force butterfly
support. They use the bounds from Section1 and explicit rectangle
arguments, not the classification of all pure fourteen-failures.
The conditional butterfly profile and Section3 of
`../invariant_structure/elementary_refinements.md` then give its
homogeneous high triples and pivot-colour low sources. The latter
section proves a refinement of a specified configuration; its
descriptive reference to observed configurations is not an exhaustion
assumption. `butterfly-plus-opposite-hand-proof.md` uses this local
refinement to give direct assemblies after any opposite is added.

## 3. The mixed loop exclusion and the new lemmas

`../mixed_diffuse/two-own-loop-triples-one-opposite-hand.md` is
a direct fourteen-adjacent-plus-one-opposite argument. It adapts
the local pure loop proof and uses only ConstructionIII in
`five-class-mixed-hand-proof.md`:3A+4disjoint+O assembles. That
construction is proved independently by a reverse-rectangle matching.
The mixed proof does not invoke the general conclusion of its own
one-opposite case, or the global fifteen-cube theorem. Its final
promotion consequence is a corollary, not an input to its proof.

The new `five-repeated-classes-two-helpers.md` uses only the
support-poset reduction, the explicit three-from-U/V constructions
from the six-doubled note, the local3,2,2,2,1 lemma, and its own
displayed geometric tables and assignments. In particular it does
not use the one-opposite result. Combined with the Section1 bounds,
it excludes the unique-triple profile3,2,2,2,2,1,1,1 by selecting
its13-source3,2,2,2,2,1,1 subpool.

The three new private-column notes use cut-incidence bounds and
direct Hall tests. The high note is independent; the diagonal note
uses its cut list; the row note reuses one Hall criterion from the
diagonal note. Their final intersecting-loop argument is just the
local universal-restoration observation, not the general mixed loop
theorem. None uses the one-opposite conclusion.

## 4. Final joining step and limits

Delete the sole opposite from a hypothetical fifteen-failure. The
fourteen adjacent sources fail, so the independent bounds apply.
The no-own-loop branch is solved by the butterfly extension lemma.
Otherwise there is one own-loop triple and, by the new13-source
lemma, another triple. The latter has a private column. If the
opposite meets it, promotion contradicts the independent mixed
two-loop theorem; if it avoids it, the three new private-column
lemmas give an assembly.

This is a complete direct fifteen-cube argument for one opposite.
The pure-fifteen synthesis note may serve as a reading guide, but
its theorem is not a premise of any step above. The proof does
not settle the classification of pure fourteen-failures with a
unique own loop, and does not require that classification.

There remain finite hand-checkable tables, notably the nine-distinct
lemma and the new five-doubled-class classification. They are explicit
proof certificates on fixed small geometric configurations. Computer
discovery or auditing of those tables does not make the proof depend
on a source-inventory search. The exploratory diffuse-eight-cube
lemma, which is still described as an exhaustive computation in its
own note, is not used anywhere in this one-opposite chain.
