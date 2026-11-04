# An elementary sharp threshold for adjacent-repeat cubes

**Theorem.** Any fifteen adjacent-repeat five-colour cubes contain eight
that assemble a five-colour 2×2×2 cube with monochromatic faces. Fourteen
do not suffice.

This proof does not use the exhaustive fourteen-cube failure list. It
also does not require finishing the classification of fourteen-failures
with exactly one own-orientation looped triple. It is a synthesis of the
written elementary lemmas indexed below; the full proof chain is longer
than this final deletion argument.

## 1. Three established facts

A tricoloured-corner class consists of three adjacent-repeat varieties
with the same six oriented tricoloured corners. Call a class *own-looped*
if, after two cubes from it are reserved, the remaining pool matches its
six tricoloured corners. The property is monotone under adding cubes.

The following results have elementary proofs.

1. **Concentration and diversity bounds.** A failing pure fourteen-pool
   has maximum class size three; a pool occupying nine distinct classes
   already has an opposite assembly; a pure fourteen-pool with six
   repeated classes assembles.
2. **No own-looped triple.** A pure fourteen-failure with no own-looped
   triple lies in a butterfly family and has class counts3,3,3,3,1,1.
3. **Two own-looped triples.** A failing pure pool of fifteen cubes, all
   class counts at most three, cannot contain two own-looped triples.

For (1), see `pure-five-class-hand.md`, the three four-copy proofs in
`../pure_supported/`, `nine-distinct-hall-proof.md`, and
`six-doubled-classes-hand.md`. For (2), see
`g3-private-column-hand.md` and its explicit dependencies. For (3), see
Section4 of `../pure_supported/two-own-loop-triples-hand.md`.

## 2. The deletion argument

Suppose a pure fifteen-cube failure exists. Every fourteen-cube subpool
is also a failure. Therefore every class has at most three copies:
any four copies could be retained in a fourteen-subpool, contradicting
the concentration bound.

At most eight classes are occupied, by the nine-distinct-class theorem.
Some class has size three. Otherwise fifteen cubes in at most eight
classes, each of size at most two, force seven doubled classes. Select
two copies from six of those classes and any two additional sources;
the resulting fourteen-pool has six repeated classes and solves.

Now take any triple class T and delete one of its cubes. The resulting
fourteen-pool still fails and has an occupied class of size two. It
cannot be a failure with no own-looped triple, since such a failure
has only triple and singleton classes. Thus it contains an own-looped
triple U≠T. The same U is own-looped in the original fifteen-pool,
by monotonicity.

Apply this argument again, now taking T=U. It produces a second
own-looped triple different from U. This contradicts fact (3).
Therefore every pure fifteen-pool assembles.

## 3. Fourteen-cube sharpness example

Here is one explicit butterfly failure. Use colours0,1,2,3,4 and the
directed-cut notation C(S)=S→Sᶜ.

| Class | Repeated colour | Number of cubes |
| --- | ---: | ---: |
| C01 | 2 | 3 |
| C02 | 1 | 3 |
| C124 | 4 | 3 |
| C123 | 3 | 3 |
| C12 | 0 | 1 |
| C012 | 0 | 1 |

Its tricoloured union misses the four arcs31,32,41,42. The bidirectional
part consists of two triangles sharing a vertex, so it contains no
four-cycle and supports no opposite target. The only adjacent target
cuts contained in the union are the six displayed classes.

The available bicoloured corners force each such target to have the
repeat listed in the table. Each high target requires its own class
at two private tricoloured positions and at both bicoloured positions,
but that class has only three cubes. Each low target requires its own
singleton at two bicoloured positions. Every target therefore fails.

This is also the derangement (1 2)(3 4) example in
`../invariant_structure/elementary_refinements.md`, Section3.

## Scope

This is a complete elementary proof of the sharp threshold in the
all-adjacent subproblem. The arbitrary five-colour theorem, including
mixed pools, has subsequently been completed; see
`fifteen-elementary-proof.md` (4 November 2026). This pure theorem
does not prove W=36 for every fourteen-failure: the unique-own-loop
pure fourteen branch remains unclassified by the present hand arguments.
