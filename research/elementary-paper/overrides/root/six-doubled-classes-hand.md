# Six doubled adjacent classes

**Elementary theorem.** Take two cubes from each of six distinct adjacent
tricoloured-corner classes. If their tricoloured-corner union supports an
opposite-repeat target, these twelve cubes assemble an opposite target.
The repeated colours within the six classes are irrelevant.

Write C(S) for the directed cut S→Sᶜ on five colours, where |S| is two
or three. Opposite targets are the eight directed edges of a bidirected
four-cycle. Only tricoloured corners are used in this proof.

## 1. A failed supported target has three private corners

Fix an opposite target T with halves P→Q and Q→P, where |P|=|Q|=2;
the fifth colour is omitted. The intersections of adjacent classes
with T have the following elementary description.

* Two classes contain the whole half P→Q, and two the whole half Q→P.
* Eight classes give a two-corner row or column in one of the two halves,
  one class for each such row or column.
* The other eight classes give four pairs crossing between the halves,
  two classes per pair. Each corner belongs to exactly one such pair.

The row/column pairs form a four-cycle in each half; the four doubled
pairs form a matching between the halves. It follows that at most three
classes have their entire intersection with T inside any prescribed
three corners, and at most two inside any prescribed two corners.
For the three-corner assertion, three corners in one half contain at
most two row/column pairs. If the corners lie in both halves, they
contain at most one row/column pair and one doubled pair.

Now each of our six classes supplies two sources. A set of one or two
target corners has enough neighbours because T is supported. A set of
five corners sees at least three classes, hence six sources: its
complement contains at most three complete source intersections.
A set of six corners similarly sees at least four classes, and a set
of seven or eight sees all six classes. Thus Hall can fail only on
three or four corners, all supplied by one class A.

Such a class must contain one whole target half, since all other
intersections have size two. In particular A has three target corners
that no other selected class contains.

## 2. Three private corners force a different opposite assembly

Reverse all cuts if necessary, and relabel colours, to put

    A=C(01),   H={03,04,13}.

Here ab denotes the directed corner a→b. The three corners H are
private to A. The classes avoiding H are exactly the following eight:

    U = { C234, C134, C123, C034 },
    V = { C13, C23, C24, C34 }.

This list follows directly from the implications 0∈S⇒3,4∈S and
1∈S⇒3∈S for an outset S of size two or three.

Our five other distinct classes therefore include three from U or
three from V. Two copies of A and two copies of any such three classes
already build an opposite target, as follows.

### Three classes from U

If C234 is present, use the target with bipartition 01∣24.
C234 supplies any two of the reverse corners {20,21,40,41}.
The other three members of U have these two-corner intersections:

| Class | Forward corner | Reverse corner |
| --- | --- | --- |
| C134 | 12 | 40 |
| C123 | 14 | 20 |
| C034 | 02 | 41 |

For either two of these classes, use one copy at its listed forward
corner and the other at its listed reverse corner. The two A copies
fill the two remaining forward corners, and the two C234 copies fill
the two remaining reverse corners.

If C234 is absent, the classes are C134,C123,C034. Use target 04∣12:

| Sources | Assigned corners |
| --- | --- |
| 2 C01 | 02,14 |
| 2 C134 | 10,42 |
| 2 C123 | 20,24 |
| 2 C034 | 01,41 |

### Three classes from V

If C13 is present, use target 01∣24. The two A copies fill 02,04,
and the two C13 copies fill 12,14. The other two classes are selected
from C23,C24,C34. C23 supplies 20,21; C34 supplies 40,41; and C24
can supply either pair. Thus the reverse half can always be filled.

If C13 is absent, use target 12∣34:

| Sources | Assigned corners |
| --- | --- |
| 2 C01 | 13,14 |
| 2 C23 | 24,31 |
| 2 C24 | 23,41 |
| 2 C34 | 32,42 |

Every case supplies a different opposite assembly. This contradicts
the assumed failure of all opposite targets, and proves the theorem.

## Scope

This is a hand proof, independent of the exhaustive fourteen-cube
classification and of the nine-distinct-classes computational lemma.
Together with the earlier elementary support-family classification,
it says that six doubled classes failing every opposite target must
be exactly a common-corner family or a butterfly family.

It does not by itself exclude all fourteen-cube pools with class
multiplicities at most two: such a pool might have fewer than six
doubled classes and correspondingly more singleton classes.

## Corollary: six repeated classes suffice in a pure fourteen-pool

**Theorem.** Fourteen adjacent-repeat cubes are soluble whenever at
least six distinct tricoloured-corner classes each occur at least twice.

In a hypothetical failure, pure concentration first bounds every class
by three: use `six-adjacent-elementary.md`, `pure-five-class-hand.md`,
and the four-copy proofs `../pure_supported/g4-row-hand.md`,
`../pure_supported/g4-hook-disjoint-hand.md`,
`../pure_supported/g4-exception-hand.md`. None uses this corollary.
Select two copies from six such classes. The theorem above solves if
their union supports an opposite target. Otherwise the support-poset theorem in
`../support_families/elementary-support-family-proofs.md` places the six distinct classes in one
of the two six-class families below; thus they fill that family exactly.

### Common-corner family

Write the common corner as a→b, and the other colours as i,j,k.
The six classes are A_i=C(ai), A_j=C(aj), A_k=C(ak), and
B_i=C(ajk), B_j=C(aik), B_k=C(aij), two copies of each.

Each A_i has a loop: after its two copies have been reserved for the
bicoloured corners, fill its six tricoloured corners by

    B_j: ij, ib;   B_k: ik, ak;   A_k: aj, ab.

Consequently, in a failure the two A_i copies must have different
repeated colours. Also A_i and A_j cannot share a repeated colour.
Indeed reserve one of each for the bicoloured corners of an A_i target,
using their common pole a. Relative to the displayed loop completion,
one universal A_i copy has been restored and one A_j copy removed;
the restored A_i can replace the removed source if it was used.
Thus the three A classes would require six different repeated colours,
which is impossible. The twelve selected cubes already solve.

### Butterfly family

Normalize the six classes to

    C01, C02, C124, C123, C12, C012.

Their union misses exactly 31,32,41,42. Any adjacent class outside
these six contains one of these four corners: avoiding all four means
being an upset of the two-below-two order, whose size-two and size-three
upsets are exactly the six listed sets.

By symmetry suppose an outside source Y contains 31. The target 03∣14
is assembled using Y and seven of the eight high-class copies:

| Sources | Corners |
| --- | --- |
| Y | 31 |
| 2 C01 | 04,13 |
| C02 | 01 |
| 2 C124 | 40,43 |
| 2 C123 | 10,34 |

Thus any outside source gives an opposite assembly. If all fourteen
sources lie within the butterfly family, the cap-three butterfly profile lemma in the same reference says that
a failure has class counts 3,3,3,3,1,1.
That is incompatible with all six classes occurring at least twice.
This proves the corollary.
