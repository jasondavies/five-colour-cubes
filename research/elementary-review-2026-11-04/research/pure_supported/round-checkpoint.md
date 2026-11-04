# Pure-adjacent structural route: checkpoint

This checkpoint records proved statements and the precise unresolved
branch. It does not assert a complete elementary proof of `N_5=15`
for arbitrary mixtures, or a complete classification of fourteen-cube
failures.

## New hand proofs in this round

| File | Statement |
|---|---|
| `two-own-loop-triples-hand.md` | A failing pure pool of fourteen or fifteen cubes, with every tricoloured class of size at most three, cannot contain two own-orientation-loop triples. |
| `private-pair-promotion-hand.md` | In a failing pure fourteen-pool with class cap three, a triple with exactly two private corners has its other four corners matched by outsiders. Adding any source meeting either private corner creates an own loop. |
| `common-corner-32221-hand.md` | Any ten sources occupying five of the six classes through one directed corner with multiplicities `3,2,2,2,1` assemble. No hypothesis on their repeated colours is needed. |
| `private-row-unconditional-hand.md` | In any failing pure fourteen-pool with class cap three, no triple has a private row pair. Every non-own-loop triple consequently has exactly two private corners. |
| `private-diagonal-unconditional-hand.md` | Every non-own-loop triple has exactly two private corners in a column, including in the unique-own-loop branch. |

The row proof also uses the companion result
`../mixed_diffuse/common-corner-3322-own-loop-hand.md`: a common-corner
`3,3,2,2` core solves if either triple has an own loop in the full pool.

The root agent has independently audited the two-own-loop proof,
the promotion proof, the `3,2,2,2,1` proof, and the unconditional row
and diagonal proofs. All explicit loops and edges in the `3,2,2,2,1` proof were also
checked against the directed-cut model: 76 witness checks across all
20 placements of the triple and singleton after normalizing the
missing class. The first diagonal draft confused row and column
pairs for negative cuts. It was replaced by a proof that excludes
the base-class triple directly and restores the original count
bounds; that full replacement passed independent root audit.

## Earlier hand results used here

The local notes `g4-row-hand.md`, `g4-hook-disjoint-hand.md`, and
`g4-exception-hand.md` settle the pure fourteen case with a four-copy
class. The root's five-copy argument and the previous larger-class
bounds remove all larger classes.

`g3-nonprivate-hand.md` gives at least two private corners to a
triple lacking an own loop. `common-corner-nine-hand.md` proves the
nine-cube common-corner theorem and its useful eight-cube cores.

The root's nine-distinct-class theorem, six-repeated-class theorem,
and all-private column classification are also established hand
inputs. The root saved the resulting pure-fifteen proof in
`../root/pure-fifteen-elementary.md`.

There is no circular use of the pure-fifteen theorem in the new
row or diagonal proofs. Their two-own-loop input is the direct
fourteen-cube argument.

## Current pure-fourteen reduction

In a hypothetical failing pure fourteen-pool, the existing results
reduce to the following conditions:

* every class has multiplicity at most three, and at least one is
  a triple;
* at most eight classes are present, and at most five classes have
  multiplicity at least two;
* at most one triple has an own-orientation loop;
* every other triple has exactly two private corners in a column;
* its other four corners have an outsider matching.

When there is no own-loop triple, the root's all-private column
proof forces the known butterfly support and failure profile
`3,3,3,3,1,1`. The case with exactly one own-loop triple has not
been structurally classified. In particular, the exploratory
observation that all remaining candidates have several triples
must not be treated as a proved lower bound on the number of
non-own-loop triples.

## Consequence for fifteen cubes with one opposite source

The mixed agent has a hand proof that any opposite source added
to a butterfly fourteen-failure gives an assembly. The mixed
two-own-loop exclusion is in
`../mixed_diffuse/two-own-loop-triples-one-opposite-hand.md`.

Thus a hypothetical remaining failure with fourteen adjacent
sources and one opposite source has a pure predecessor with a
unique own-loop triple U. This loop persists after adjoining the
opposite source. For every other triple T, the promotion lemma
implies that the opposite source must avoid both corners of T's
private column; otherwise T gains an own loop as well and the
mixed two-own-loop theorem solves the pool.

For example, if `T=C(01)` has private column `02,12`, an opposite
source avoiding both corners has exactly five possibilities:

* it omits colour 2, with any of the three pairings of `0,1,3,4`;
* it omits colour 0 and has pair partition `12|34`;
* it omits colour 1 and has pair partition `02|34`.

These are model target/source indices `60,63,66,67,68`. To check
the classification directly, if colours `0,1,2` all occur, avoiding
both arcs would require 2 to share its pair with both 0 and 1,
which is impossible. Omitting 0 or 1 determines the remaining
pairing; omitting 2 removes both corners automatically.

**Precise remaining local gap.** Exclude the unique-own-loop pure
fourteen predecessor after adjoining an opposite source that
avoids every other triple's private column. A structural proof
must also cover a predecessor with no other triple, unless a
separate lemma first proves that such a predecessor cannot fail.

## Discovery output is not part of the proof

The `own-loop-*.json*` files and `own_loop_sweep.cpp` were used to
discover useful configurations. They are not being substituted for
the unresolved structural classification. The new proof notes rely
on explicit matchings, short class-capacity inequalities, and
repeated-colour pigeonhole arguments only.
