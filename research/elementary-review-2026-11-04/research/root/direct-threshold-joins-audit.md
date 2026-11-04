# Independent audit of the final direct-threshold joins

4 November 2026

**Outcome: PASS.** This audit checks theorem scopes, source counts,
physical-source lifting, and dependency order in:

- `three-opposites-eleven-adjacent.md`;
- `two-opposites-thirteen-adjacent.md`;
- the class-cap-three strengthening in `five-opposites-nine-adjacent.md`.

The component geometric and numerical proofs have already passed
independent audits. This final check uses their proved statements;
it does not repeat diagnostic searches.

## 1. Three opposites and eleven capped adjacent sources

The opposite multiplicity partitions are exactly1,1,1;2,1;3.
The distinct and doubled component theorems both accept eleven
adjacent sources with class cap three and arbitrary actual repeated
colours. Both permit either an adjacent or an opposite target, as
the joined theorem correctly states.

For three identical opposites, the earlier concentrated fourteen-
failure classification forces adjacent profile5,3,3. In the present
pool the opposite total is exactly three, so the separate four-
opposite family cannot intervene. The profile5,3,3 contradicts
class cap three. Thus no opposite multiplicity restriction remains.

Neither diffuse component uses the two-opposite fifteen theorem.
The concentrated component is an earlier Hall-cover classification,
independent of the general threshold. The join is acyclic.

The immediate fifteen-source consequence is valid: with three
opposites and twelve adjacent sources, remove one adjacent source.
Class cap three is retained.

## 2. Two opposites and thirteen capped adjacent sources

For disjoint adjacent cuts A,B, the stated normalization and complete
list of disjoint classes give an opposite variety U with
all eight tricoloured corners in A∪B. Removing one actual source
from each class and inserting one virtual U gives exactly three
opposites and eleven adjacent sources. Adjacent counts only decrease.
The new three-opposite theorem explicitly includes the possibility
that all three opposite varieties coincide after this replacement.

In any resulting assembly, the virtual opposite can occupy only a
tricoloured position, including when the target is adjacent. At that
one position a removed physical A or B supplies the required corner.
Both removed cubes were absent from every other assignment. Thus
replacement preserves eight distinct physical sources and compatible
proper rotations. If U is unused, no replacement is needed.

Without a disjoint pair, the geometric containment theorem applies
to the occupied cut support. Its statement includes partial and
empty signed edge families. The three containing families therefore
exhaust the remaining support geometry. Each numerical family lemma
permits zero counts, arbitrary counts up to three summing to thirteen,
and arbitrary two opposite sources, including coincident varieties.
The hypotheses match exactly.

Only the compression branch uses the three-opposite theorem. The
three family closures use the independently proved common-corner
eleven-source lemma and local matchings or repeated-colour cores.
None assumes this two-opposite conclusion or the general threshold.

## 3. Five opposites and the adjacent class-cap-three strengthening

The earlier audited helper lemma is independent of any cap on the
rest of an adjacent pool. It assumes five opposite sources of
variety cap two and adjacent sources2A+B+C, with A,B,C distinct,
and gives an opposite target using2A and one helper.

Now take nine adjacent sources of class cap three. If all nine
classes are distinct, the nine-distinct-class theorem supplies an
opposite target. Otherwise choose two sources from one class A.
At least three classes occur because two capped classes hold at
most six of the nine sources. Hence two distinct other classes B,C
are available, and the unchanged helper lemma applies. The two A
sources may have different repeated colours, since every target
corner in that argument is tricoloured.

This proves the cap-three strengthening with the same opposite-
target conclusion. It does not invoke the stronger universal
eight-source claim for an arbitrary single helper.

For fifteen-source totals five or six, selecting five opposite and
nine adjacent sources is legitimate: there are respectively ten
or nine adjacent sources, and both multiplicity caps are retained.
References to the final threshold in the consequences section are
applications of the theorem, not premises of its proof.

## 4. Dependency order

The relevant order is: earlier geometric/concentration/local lemmas;
independent three-opposite and five-opposite results; the two-
opposite compression-and-family theorem; then the fifteen-source
case split. The one-opposite route has its own independent dependency
audit in `../elementary_alternative_next/audit-one-opposite-dependencies.md`.

No join here assumes N5=15, the global fourteen-failure identity,
or an exhaustive cube-inventory catalogue. All three requested
checks pass without changes to their mathematical arguments.
