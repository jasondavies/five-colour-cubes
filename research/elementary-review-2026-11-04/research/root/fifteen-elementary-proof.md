# A direct elementary proof of the five-colour threshold

4 November 2026

**Status: complete elementary proof, assembled from the written
component lemmas.** Every new numerical branch has completed
independent mathematical audits, including the last star-and-triangle
two-opposite case. The final synthesis has also passed an independent
joining audit, recorded in
[audit-fifteen-elementary-master.md](../three_opposite_double/audit-fifteen-elementary-master.md).

The conclusion is

\[
N_5=15.
\]

The route uses written geometric lemmas, Hall's theorem, and elementary
counting. It does not assume the exhaustive fourteen-cube failure
catalogue or the identity \(3A-4B=36\). This is a synthesis of the
component hand proofs, whose combined length is substantial; it is
not a claim to have found a short proof. No new Lean formalisation
is asserted.

## 1. Definitions and the corner model

Fix the five colours \(V=\{0,1,2,3,4\}\). Each source cube uses all
five colours on its six faces, so precisely one colour occurs twice.
Call the cube *adjacent* or *opposite* according as these two faces
are adjacent or opposite. A variety is a colouring considered up to
proper rotations.

An assembly selects eight distinct physical sources and independently
rotates them to form a \(2\times2\times2\) cube whose six exterior
faces are monochromatic and together use all five colours. Its target
may be adjacent or opposite. Write \(N_5\) for the least number of
arbitrary source cubes that always contains such an assembly. A pool
*fails* if it has no assembly. Every subpool of a failure also fails.

Encode a cyclic tricoloured corner \((i,j,k)\) by its complementary
directed pair \(a\to b\), choosing the order so that
\((a,b,i,j,k)\) is an even permutation of the five colours. Cyclic
rotation preserves this parity. We abbreviate this directed corner
to \(ab\).

An adjacent tricoloured-corner class is a directed cut

\[
C(S)=\{ab:a\in S,\ b\notin S\},\qquad |S|=2\text{ or }3.
\]

Its *pole pair* \(P\) is the two-element side of the cut. Each class
has three varieties, one for each repeated colour \(r\notin P\).
In addition to their common six tricoloured corners, the variety
repeating \(r\) has the two bicoloured corners \((r,r,p)\), for
\(p\in P\). There are twenty adjacent classes and sixty adjacent
varieties. A class count always counts actual cubes, possibly from
different varieties within that class.

An opposite variety is a four-cycle on four colours, omitting its
repeated colour. It supplies both directed corners on each of its
four edges. Equivalently, its edges form \(K_{2,2}\) between two
disjoint pairs. There are fifteen opposite varieties.

For a fixed target, a matching of its eight corner types to eight
distinct sources is equivalent to an assembly: each matched source
has a compatible proper rotation at its assigned corner. All the
proofs below use this criterion. Reflections used to normalize a
whole configuration are not permitted moves on individual sources.

Write \(o\) for the total number of opposite sources, \(g_j\) for
the twenty adjacent-class counts, and

\[
A=\sum_j\binom{g_j}{2},\qquad B=\binom{o}{2},\qquad W=3A-4B.
\]

For later discussion, a triple class is *own-looped* if reserving
two of its cubes still leaves a matching of its six tricoloured
corners. This condition alone does not claim that the reserved cubes
fit the same target's two bicoloured corners.

## 2. Concentration reductions for a hypothetical fifteen-failure

### 2.1. Every opposite variety has multiplicity at most two

The older elementary classifications have the following consequence
for any fourteen-failure containing at least three copies of one
opposite variety:

| Opposite sources | Adjacent-class sizes |
| --- | --- |
| Four copies of one variety, no other opposite source | \(5,5\) |
| Three copies of one variety, no other opposite source | \(5,3,3\) |

No opposite variety can occur five times in a fourteen-failure.
The proofs are in [o4-elementary.md](o4-elementary.md) and
[o3-covers-guide.md](o3-covers-guide.md), with their listed geometric
dependencies. These classifications do not use the general threshold.

Suppose a fifteen-failure contained at least three copies of some
opposite variety \(O\). Five copies could be retained in a
fourteen-subpool, which is impossible. Thus the multiplicity of
\(O\) is three or four. There cannot be another opposite variety:
retain three copies of \(O\) and a copy of that other variety in a
fourteen-subpool, contradicting the classification. The opposite
total is therefore exactly three or four, all of variety \(O\).

If there are four copies of \(O\), delete each of the eleven
adjacent cubes in turn. Every resulting fourteen-failure has
adjacent profile \((5,5)\), so its value of \(A\) is twenty.
Each pair of adjacent physical cubes in the original pool survives
exactly nine of these deletions. Double-counting gives

\[
9A_{15}=11\cdot20=220,
\]

which is impossible because \(A_{15}\) is an integer.

If there are three copies of \(O\), delete each of the twelve
adjacent cubes instead. Each resulting profile is \((5,3,3)\),
whose value of \(A\) is sixteen. Each original adjacent pair
survives ten deletions, giving

\[
10A_{15}=12\cdot16=192,
\]

again impossible. Hence every opposite variety in a fifteen-failure
has multiplicity at most two.

### 2.2. Every mixed adjacent class has multiplicity at most three

The completed mixed concentration theorem says that a fourteen-pool
with at least one opposite source, opposite-variety cap two, and
four cubes in one adjacent class assembles. Its component proofs,
including the one-opposite case, are indexed in
[PROOF-CHECKPOINT.md](../mixed_diffuse/PROOF-CHECKPOINT.md).

If a mixed fifteen-failure had four cubes in one adjacent class,
retain those four and an opposite source in a fourteen-subpool.
Section 2.1 supplies its opposite cap two. The mixed concentration
theorem gives a contradiction. Thus every mixed fifteen-failure
satisfies \(g_j\le3\) for every adjacent class.

The order of these reductions matters: the opposite cap is proved
first and is a hypothesis of the mixed concentration theorem.

## 3. The uniform three-opposite lemma

The theorem in
[three-opposites-eleven-adjacent.md](three-opposites-eleven-adjacent.md)
states:

> Any three opposite cubes and eleven adjacent cubes with
> adjacent-class cap three contain a five-colour assembly.

There is no opposite-variety multiplicity restriction. The two new
hand proofs cover three distinct varieties and the profile \((2,1)\).
Three identical opposites are covered by the earlier classification:
a failing fourteen-pool would require adjacent profile \((5,3,3)\),
contradicting the class cap. The referenced note contains the complete
joining argument and audit records; no branch is being inferred from
computation here.

## 4. Two opposite cubes and thirteen capped adjacent cubes

This section proves that row of the threshold. The same closure is
packaged as a standalone theorem in
[two-opposites-thirteen-adjacent.md](two-opposites-thirteen-adjacent.md).

### 4.1. Compress a disjoint pair of cuts

Suppose two actual adjacent sources have disjoint tricoloured cuts
\(A,B\). After normalizing \(A=C(01)\), the possibilities for
\(B\) are exactly

\[
C(234),\quad C(23),\quad C(24),\quad C(34).
\]

For \(B=C(ij)\), with \(i,j\in\{2,3,4\}\), the opposite
variety between the pairs \(01\) and \(ij\) has all eight corners
in \(A\cup B\). For \(B=C(234)\), use any two of \(2,3,4\).

Remove those two actual sources and introduce one virtual source of
this opposite variety. There are now three opposite and eleven
adjacent sources; adjacent class counts have only decreased. Apply
Section 3. If the virtual source is used, its one assigned corner
belongs to \(A\) or \(B\), so replace it by the corresponding
removed actual source. Neither actual source occurs elsewhere in
the assignment. If the virtual source is unused, no replacement is
needed. Its position is necessarily tricoloured, so the actual
sources' repeated colours do not affect this replacement.

Thus an assembly in the compressed pool gives an assembly using
eight distinct physical sources in the original pool. The three
opposite sources may become identical during compression; Section 3
explicitly includes that case.

### 4.2. The three intersecting families

It remains that every two occupied adjacent cuts intersect. Regard
a cut of outset size two as a positive pole pair, and a cut of
outset size three as a negative pole pair. Two cuts of the same
sign are disjoint precisely when their pole pairs are disjoint;
oppositely signed cuts are disjoint precisely when their pole pairs
are equal.

Thus the positive and negative pole pairs are two intersecting
edge families in \(K_5\), with no edge in both families. An
intersecting edge family is contained in a star or a triangle.
Combining these two possibilities shows that, up to colour
relabelling and global reversal, the occupied cuts are contained
in one of the following three families:

| Family | Allowed adjacent classes |
| --- | --- |
| Two stars | \(C(01),C(02),C(03),C(04),C(034),C(024),C(023)\) |
| Butterfly | \(C(01),C(02),C(12),C(123),C(124),C(012)\) |
| Star and triangle | \(C(01),C(02),C(03),C(04),C(034),C(024),C(014)\) |

The full elementary containment proof, including empty or small
signed families, is in
[pair-compression-and-intersecting-cuts.md](../three_opposite_root/pair-compression-and-intersecting-cuts.md).
The statement is containment, so zero counts in a listed family
are allowed.

For each family we need the assertion that thirteen sources of
class cap three, together with any two opposite sources, assemble.
The two opposite varieties may coincide.

| Family | Numerical proof | Status |
| --- | --- | --- |
| Two stars | [two-star-two-opposites.md](../three_opposite_distinct/two-star-two-opposites.md) | Complete; independent root audit passed |
| Butterfly | [butterfly-two-opposites-thirteen-adjacent.md](../elementary_alternative_next/butterfly-two-opposites-thirteen-adjacent.md) | Complete; independent mathematical audit passed |
| Star and triangle | [star-triangle-thirteen-adjacent-hand.md](../three_opposite_double/star-triangle-thirteen-adjacent-hand.md) | Complete; independent root and second-agent audits passed |

The disjoint-pair and intersecting-family alternatives exhaust the
two-opposite case, proving the required fifteen-source statement.

## 5. Joining the cases to obtain the threshold

**Theorem.** Every fifteen five-colour cubes contain an assembly.

Suppose otherwise. Section 2.1 gives opposite-variety cap two.
Whenever the pool is mixed, Section 2.2 also gives adjacent class
cap three. Split by its opposite total \(o\).

| \(o\) | Contradiction to failure |
| ---: | --- |
| \(0\) | The pure fifteen-cube theorem in [pure-fifteen-elementary.md](pure-fifteen-elementary.md). |
| \(1\) | The unrestricted one-opposite/fourteen-adjacent theorem in [one-opposite-fourteen-adjacent.md](../elementary_alternative_next/one-opposite-fourteen-adjacent.md). |
| \(2\) | [two-opposites-thirteen-adjacent.md](two-opposites-thirteen-adjacent.md), proved in Section 4 by compression or the three intersecting-family lemmas. |
| \(3\) or \(4\) | Select three opposite and eleven adjacent cubes, and apply Section 3. For \(o=3\), discard one adjacent cube; for \(o=4\), discard one opposite cube. |
| \(5\) or \(6\) | Select five opposite cubes and nine adjacent cubes, and apply the helper argument just below. |
| \(7\) | Seven capped opposite cubes and any one adjacent cube assemble, by the corollary in [eight-opposite-elementary.md](eight-opposite-elementary.md). |
| \(8\) or more | Select eight opposite cubes and apply the capped eight-opposite theorem in the same note. |

For the \(o=5,6\) rows, the nine selected adjacent sources retain
class cap three. If they are in nine distinct classes, use
[nine-distinct-hall-proof.md](nine-distinct-hall-proof.md). Otherwise
some class \(A\) occurs twice. At least three classes occur, since
no class has more than three sources, so choose one source from each
of two different other classes \(B,C\). The helper lemma in
Section 3 of
[five-opposites-nine-adjacent.md](five-opposites-nine-adjacent.md)
gives an assembly from

\[
5\text{ capped opposite sources}+2A+B+C.
\]

This argument covers both rows without a separate adjacent-triple
case. Equivalently, apply the strengthened class-cap-three theorem
in [five-opposites-nine-adjacent.md](five-opposites-nine-adjacent.md).
The independent four-opposite/ten-adjacent and six-opposite/fourteen-
source results remain stronger fourteen-source conclusions, but
neither is necessary for this threshold proof.

Every value of \(o\) gives a contradiction. Hence \(N_5\le15\).

### Sharpness

Section 3 of
[pure-fifteen-elementary.md](pure-fifteen-elementary.md) gives and
proves the following fourteen-cube obstruction:

| Adjacent class | Repeated colour | Multiplicity |
| --- | ---: | ---: |
| \(C(01)\) | \(2\) | \(3\) |
| \(C(02)\) | \(1\) | \(3\) |
| \(C(124)\) | \(4\) | \(3\) |
| \(C(123)\) | \(3\) | \(3\) |
| \(C(12)\) | \(0\) | \(1\) |
| \(C(012)\) | \(0\) | \(1\) |

Its bidirectional tricoloured support is two triangles meeting at
one vertex, so it contains no opposite target. The only contained
adjacent target classes are the six displayed ones. Their
bicoloured requirements force the repeats in the table. A high
class would have to supply two private tricoloured positions and
both bicoloured positions, but has only three cubes; a low class
would need two copies for its bicoloured positions, but has only
one. Thus no target assembles, and \(N_5\ge15\).

Combining the upper and lower bounds gives \(N_5=15\).

## 6. Acyclic dependency order

The dependency order for this synthesis is as follows. A later row
may use an earlier one, but no earlier row uses the final threshold.

1. **Geometry and local tools.** The directed-corner model, Hall's
   theorem, matching-rank facts, explicit repeated-colour restoration,
   and the paper's independent eight-plus-three common-missing-pair
   lemma. The latter enters the old concentrated opposite branch;
   a self-contained version, including the projection calculation,
   is in
   [eight-plus-three-common-missing-pair.md](eight-plus-three-common-missing-pair.md).
   It is the paper's Lemma `lem:eight-common-missing` and does not
   assume \(N_5=15\).
2. **Older structural theory.** Opposite concentration, mixed
   adjacent concentration, pure fourteen-cube concentration and
   private-corner results, the support-poset theorem, and the small
   common-corner constructions. These also give the pure fifteen
   theorem and the explicit lower-bound example.
3. **New local lemmas.** Eleven capped adjacent cubes sharing a
   corner assemble; the thirteen-source adjacent profile
   \((3,2,2,2,2,1,1)\) assembles; and the explicit nine-source
   repeated-colour core. The proofs are respectively
   [common-corner-eleven-hand.md](../three_opposite_double/common-corner-eleven-hand.md),
   [five-repeated-classes-two-helpers.md](../elementary_alternative_next/five-repeated-classes-two-helpers.md),
   and Sections 1–2 of
   [repeated-colour-closures.md](../three_opposite_root/repeated-colour-closures.md).
4. **Independent numerical branches.** The one-opposite fifteen
   theorem uses pure predecessor structure and three private-column
   lemmas. The uniform three-opposite fourteen theorem uses its
   distinct and doubled branches, the local lemmas, and the old
   concentrated classification. The five-, seven-, and eight-
   opposite results are independent of the two-opposite
   fifteen theorem.
5. **The two-opposite fifteen theorem.** Disjoint-pair compression
   uses the already proved uniform three-opposite theorem. The
   intersecting-family classification is unconditional geometry;
   its three numerical closures use earlier local lemmas and
   explicit assignments.
6. **The threshold.** Concentrated fifteen-failures are excluded
   by the two deletion equations in Section 2. The case split in
   Section 5 then uses only the preceding results.

In particular, the three-opposite result does not depend on the
two-opposite conclusion reached by compression. The one-opposite
proof does not depend on either. The stronger global identity for
fourteen-failures is outside this dependency chain.

Diagnostic programs helped discover and check small geometric facts
and displayed matchings. The cited hand arguments provide the case
exhaustions; no inventory-search output is used as a substitute for
a missing case. The final star-and-triangle component has completed
two independent mathematical audits, so no numerical branch remains
conditional in this synthesis.

## 7. What remains for the global fourteen-failure identity

The direct threshold argument does not prove that every failing
fourteen-pool satisfies \(W=36\). The precise remaining scope of
that separate question is:

| Opposite total in a fourteen-failure | Present status for \(W=36\) |
| ---: | --- |
| At least \(5\) | No failures, by the existing large-opposite results and concentration. |
| \(4\) | Fully classified: four copies of one opposite variety and adjacent counts \((5,5)\). Thus \(W=3\cdot20-4\cdot6=36\). |
| \(3\) | Fully classified: three identical opposites and adjacent counts \((5,3,3)\). The new uniform theorem excludes capped adjacent cases; concentration excludes the others unless they are this old family. Thus \(W=3\cdot16-4\cdot3=36\). |
| \(2\) | The remaining question is to exclude every pool of two opposite and twelve adjacent cubes with adjacent cap three. Here \(W=3A-4\), which can never equal \(36\) for integral \(A\); the identity requires that this failure branch be empty. |
| \(1\) | One opposite and thirteen adjacent cubes with class cap three remain to be classified, or at least shown to have \(A=12\) whenever they fail; this is equivalent to adjacent profile \((3,3,3,3,1)\). |
| \(0\) | The no-own-loop branch is already classified and has profile \((3,3,3,3,1,1)\), hence \(A=12\). The pure fourteen branch with a unique own-looped triple remains for the identity; the new thirteen-source lemma does show that such a failure must have another triple. |

For the \(o=3\) row, a diffuse failure first has adjacent cap three
by mixed concentration and then contradicts Section 3. A concentrated
failure is exactly the older \((5,3,3)\) family. No assumption about
the unresolved \(o=1,2\) rows is needed for this classification.

The original deletion-and-divisibility idea remains valid: if
\(W=36\) were known for every fourteen-failure, then deleting each
cube of a fifteen-failure would give

\[
13W_{15}=15\cdot36=540,
\]

which is impossible for integral \(W_{15}\). Each pair contributes
to exactly thirteen deletions. The direct proof above bypasses the
three remaining fourteen-source branches instead of establishing
that identity.
