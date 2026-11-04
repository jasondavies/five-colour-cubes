# Independent audit: the butterfly two-opposite fifteen-cube branch

4 November 2026

**Result: passed.** The complete argument in
`../elementary_alternative_next/butterfly-two-opposites-thirteen-adjacent.md`
is valid. Its reduction is exhaustive, every source count is respected,
and its final repeated-colour construction uses eight distinct actual
sources. No inventory enumeration enters the proof or this audit.

## 1. Common-corner reductions

The four stated common-corner families are correct. The complements
of A,L,U,V; A,M,U,V; P,L,U,V; P,M,U,V are the four opposite high
pairs. Since the whole adjacent pool has thirteen sources, excluding
an eleven-source common-corner subpool gives precisely

    a+l≥3, a+m≥3, p+l≥3, p+m≥3.

The butterfly union misses exactly31,32,41,42. An opposite variety
avoiding all four would be a four-cycle in the graph formed by the
two triangles012 and034 meeting only at0. Every simple cycle in
that graph lies in one triangle, so no such opposite variety exists.

## 2. All four high classes occur

If neither high pair A,P nor L,M has both counts at least two,
one count in each pair is one, contradicting the corresponding
cross-pair inequality. The low total u+v is positive because four
high counts of at most three cannot total thirteen.

The stated permutation followed by direction reversal exchanges
A with L, P with M, and U with V. It permits the normalization
l,m≥2. The independent swaps of1,2 and3,4 preserve that condition
and act transitively on the four missing corners.

Assignment (2) is correct on target03|14: O:31, P:01, L:40,43,
M:10,34, A:04, and either low class:13. The seven adjacent sources
respect the normalized lower bounds and the opposite source is a
separate eighth cube. Thus one opposite source suffices in this case.

## 3. A high class is absent

The same symmetries are transitive on the four high classes. Setting
a=0 forces l=m=3. The remaining equation p+u+v=7 with each count
at most three forces all three to be positive.

Assignment (4) correctly replaces A:04 by V:04 and uses U:13.
Swapping3,4 covers corner41. Hence both opposite sources can be
assumed to avoid underlying edges13,14.

The five-variety classification is complete. An opposite cube omitting1
has one of the three partitions of0234. Otherwise vertex1 must have
neighbours0,2; its same-part vertex is3 or4, giving exactly the
remaining two varieties R,S. The table correctly records which of
32 and42 each supplies.

If the two sources can match32,42, target02|34 is completed by
M:30, L:40, and four P,V sources on03,04,23,24. The inequality
p+v=7−u≥4 is sufficient, and those four sources are distinct from
L,M and the opposite sources.

Failure of that two-position matching leaves precisely two sources
from {Y,S} or two from {Z,R}; a source X supports both positions
and cannot occur in a failed pair. Swapping3,4 exchanges the two
remaining alternatives.

If Y occurs, assignment (5) uses that actual source at02 and the
other actual opposite source at32. It remains valid when both
sources are Y. Its three L assignments40,43,20 use exactly the
available three copies; P,M,U each contribute one.

For two copies of S with p≥2, assignment (6) uses two actual S,
two P, two M, one V, and one U. All eight corners of02|13 occur
exactly once. Therefore the sole residual is p=1 and l=m=u=v=3,
with two S sources, exactly as stated.

## 4. The final repeated-colour argument

The M matching (8) is its exact six-corner set
{10,14,20,24,30,34}; the V matching (9) is its exact six-corner
set{03,04,13,14,23,24}. Each uses only the one available P source,
two of three L sources, at most one opposite source, and no more
copies of any other class than remain after reservation.

Thus a failure forces the M triple to use repeats1,2,3 and the V
triple to use repeats0,1,2. The selected M repeat1 source supplies
the bicoloured pole0 corner of the M target; the selected V repeat1
source supplies its pole4 corner. Matching (8) uses no V at all
and needs only one of the two still available M sources. The other
assigned cubes are unchanged and distinct. This is a valid eight-
source assembly, giving the required contradiction.

## Dependency check

The proof depends only on the common-corner eleven-source lemma,
the basic directed-cut geometry, and explicit assignments. It does
not use the three-opposite theorem, pair compression, the full
two-opposite theorem, the pure fourteen-failure classification, or
the desired N5=15 conclusion. It can therefore be placed before
the two-opposite compression argument in an acyclic presentation.
