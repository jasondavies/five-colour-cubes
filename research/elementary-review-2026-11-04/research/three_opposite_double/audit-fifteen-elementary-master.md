# Independent audit of the direct fifteen-cube synthesis

4 November 2026

**Result: the joining proof in `../root/fifteen-elementary-proof.md`
passes mathematical audit.**

The audit checks that the previously established component theorems
are applied with their actual hypotheses, that the new reductions
are valid, and that the fourteen-cube lower bound is proved directly.
It does not substitute an inventory computation for any component
lemma, and it does not claim a new Lean verification. The component
hand proofs and their independent audits remain part of the proof.

## 1. Opposite concentration and deletion counts

The older fourteen-source classifications give the two profiles

    4O + adjacent profile(5,5),
    3O + adjacent profile(5,3,3),

and exclude five identical opposite sources and any additional
opposite variety when three copies of O occur.

The fifteen-source inference preserves the required specified
sources in a fourteen-subpool. Thus a hypothetical fifteen-failure
containing three equal opposites has exactly three or four opposite
sources, all equal. There is no omitted case with a fifth copy or
another opposite variety.

With four opposites there are eleven adjacent sources. An unordered
pair of these survives exactly nine of the eleven single-adjacent
deletions. Every resulting profile(5,5) has pair count20, yielding
9A=220, which has no integral solution.

With three opposites there are twelve adjacent sources. Each pair
survives ten of the twelve deletions, and every profile(5,3,3) has
pair count16. Hence10A=192, again impossible.

The mixed adjacent-class cap is then applied in the correct order:
retain four copies of one adjacent class and an opposite source in
a fourteen-subpool. The already established opposite cap two is
inherited by that subpool. The mixed concentration theorem applies.

## 2. The uniform three-opposite input

The theorem used has no restriction on the three opposite varieties.
Its distinct and doubled cases are independently proved; the three
equal case follows from the old profile(5,3,3) classification and
contradicts adjacent class cap three. This unrestricted version is
essential for the virtual-source step. The master uses the correct
version, rather than only the diffuse cases.

## 3. Disjoint-pair compression and the two-opposite branch

After normalizing A=C(01), a cut disjoint from A must have its
outset contained in234. The only size-two or size-three choices are
23,24,34,234. This establishes the exact four alternatives directly.

For B=C(ij), the target01|ij has its four forward corners in A
and four reverse corners in B. The same holds for B=C(234) after
choosing any two of2,3,4. Removing both physical sources before
introducing one virtual opposite source preserves source distinctness
when the virtual source's single corner is replaced. If the virtual
source is unused, the assignment already uses physical sources only.
An opposite source cannot occupy a bicoloured position, so no
repeated-colour issue is concealed in the replacement.

The compressed pool has exactly3O+11A and retains adjacent class cap
three. No opposite cap is needed at this stage. If no disjoint pair
exists, the signed star/triangle containment argument applies. Each
of its three numerical family lemmas permits zero class counts and
arbitrary two-opposite multiplicities. Thus the alternatives really
exhaust the two-opposite branch.

The star-and-triangle proof was separately audited by both root and
the alternative agent before this joining audit. Its only earlier
inputs are common-corner eleven and the nine-source repeated-colour
construction, so its use here introduces no cycle.

## 4. The grouped opposite-total cases

All source selections preserve the appropriate class and variety
caps.

* For o=3, the pool has twelve adjacent sources. Delete one adjacent
  source and apply the3O+11A theorem.
* For o=4, the pool has eleven adjacent sources. Delete one opposite
  source and apply the same theorem. The separate4O+10A result is
  not needed for this threshold.
* For o=5, select five opposites and nine of the ten adjacent cubes.
* For o=6, select five of the six opposites and all nine adjacent
  cubes.

In each of the last two cases, nine distinct adjacent classes already
solve. Otherwise select two copies in one class A. At least three
classes occur because the cap is three and the adjacent total is
nine. Therefore there exist two distinct other occupied classes B,C.
The audited helper lemma applies to5O+2A+B+C, with opposite variety
cap two, and uses just one of the two helper sources. No third copy
of A is assumed. This is why the grouped o=5,6 reduction is valid
under cap three and requires no separate triple-class argument.

At o=7 an adjacent cube exists and the seven-opposite corollary
applies. At o≥8, select eight capped opposite cubes. The o=0 and
o=1 rows invoke the pure fifteen-source theorem and the unrestricted
one-opposite/fourteen-adjacent theorem, respectively. These statements
have the required scope. The table therefore covers every total
from zero to fifteen.

## 5. Direct verification of the sharpness example

For the listed six adjacent classes the tricoloured union is exactly
the twenty directed pairs except31,32,41,42. Its bidirected edges
are

    01,02,12 and 03,04,34.

They form the triangles012 and034 meeting at0 and contain no
four-cycle. No opposite target is therefore supported.

A supported adjacent cut C(S) must satisfy

    3 in S implies 1,2 in S,
    4 in S implies 1,2 in S.

For |S|=2 or3 these conditions give exactly

    S=01,02,12,012,123,124.

Indeed, if neither3 nor4 lies in S, take the size-two or size-three
subsets of012. If exactly one lies in S, its two forced companions
give123 or124. Both cannot lie in S because then S would have at
least four elements. This proves that no adjacent target class was
omitted.

For completeness, the available bicoloured corners can be written
as pairs(r,p), encoding(r,r,p):

| Source class | Repeat r | Available pole colours p |
| --- | --- | --- |
| C01 | 2 | 0,1 |
| C02 | 1 | 0,2 |
| C124 | 4 | 0,3 |
| C123 | 3 | 0,4 |
| C12 | 0 | 1,2 |
| C012 | 0 | 3,4 |

For each of the six target classes, only its listed repeat supplies
both required pole colours. Both bicoloured positions then require
sources from that same class. For a high class, two tricoloured
positions are private to it as well:

| High class | Its two private tricoloured corners |
| --- | --- |
| C01 | 02,12 |
| C02 | 01,21 |
| C124 | 40,43 |
| C123 | 30,34 |

Each such target would require four distinct sources from a class
with only three copies. Each low target would require two sources
from a singleton class for its bicoloured positions alone. All
possible targets fail. This establishes N5≥15 directly, without
consulting a failure catalogue.

## 6. Dependency and scope check

The synthesis is acyclic. The old concentrated classifications and
the mixed cap theorem precede the numerical threshold. The uniform
three-opposite theorem is independent of the two-opposite result;
the latter alone invokes compression. The one-opposite proof relies
on pure predecessor structure, the thirteen-source local lemma and
private-column arguments, not on the general threshold. The five-,
seven- and eight-opposite theorems are also independent inputs.

The invariant discussion is correctly separated from the threshold:
the o=3 and4 profiles give W=36; for o=2, the identity would require
3A−4=36 and is arithmetically impossible for integral A; for o=1 it
requires A=12. A proof of the threshold does not establish these
remaining fourteen-source statements. The conditional deletion
identity13W15=540 is also correct: every pair survives thirteen
single-source deletions.

No mathematical gap was found in the final joining argument.
