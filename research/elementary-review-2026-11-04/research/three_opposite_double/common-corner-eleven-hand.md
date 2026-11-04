# Eleven adjacent cubes through one directed corner

4 November 2026

**Status: elementary proof; independent root audit passed.**

**Theorem.** Eleven adjacent-repeat cubes whose tricoloured-corner
classes all contain one fixed directed corner assemble a five-colour
target, provided every class has multiplicity at most three.

No opposite sources are required. The argument uses only small
six-corner matchings and the previously proved common-corner lemmas.
The opposite-target failure catalogue is not a premise.

## 1. Reduction to two multiplicity patterns

There are six classes containing a given directed corner. If all six
occur, select nine cubes preserving all six classes and apply
`../pure_supported/common-corner-nine-hand.md`.

If five classes occur, their positive counts, each at most three and
totalling eleven, are exactly

    3,3,3,1,1;  3,3,2,2,1;  3,2,2,2,2.

The latter two contain a 3,2,2,2,1 subpool and are solved by
`../pure_supported/common-corner-32221-hand.md`.

If four classes occur, the counts are 3,3,3,2. At most three classes
cannot accommodate eleven cubes. Thus only 3,3,3,2 and 3,3,3,1,1
remain.

We use an **own loop** to mean a matching of all six tricoloured
corners of a class after reserving two copies of that class. In a
failure, an own-looped triple must use all three of its allowed
repeated colours. Classes **conflict** when reserving one cube of
each with a common repeated colour permits the six-corner completion
of a target whose two poles the reserved cubes supply. Conflicting
classes must have disjoint repeated-colour sets.

An own-loop class conflicts with every present class whose pole pair
intersects its own. To prove this, restore one of the reserved own
class copies, remove the other class's reserved source, and replace
that source in the matching by the restored universal source if
necessary. This is the usual universal-restoration argument.

## 2. Four classes of sizes 3,3,3,2

Normalize the common corner to 01. Write Q={2,3,4}, and put

    P_i=C(0i),    D_i=C({0}∪(Q\{i})).

Arbitrary permutations of Q and interchange of the P and D families
give exactly three forms for a four-class support:

    {P4,D2,D3,D4},
    {P3,P4,D3,D4},
    {P3,P4,D2,D4}.

These correspond to the two missing classes being of one kind,
matched across kinds, or unmatched across kinds.

In each form at least one of the three triples has an own loop.

* For {P4,D2,D3,D4}, at least one of D2,D3 is a triple. If D2 is
  a triple, reserve two copies and match

      D2:32; P4:02,42; D4:31; D3:41,01.

  The case of a D3 triple follows by interchanging 2 and 3.

* For {P3,P4,D3,D4}, at least one of the pairs {P3,D4} and
  {P4,D3} consists of two triples. In the former case, reserve two
  P3 and match

      P3:32; D4:04,31,34; P4:02; D3:01.

  The other pair follows by interchanging 3 and 4.

* For {P3,P4,D2,D4}, both P3 and D2 have own loops already when
  each class has only two copies. The explicit completions are in
  Section 4 of `../mixed_diffuse/common-corner-3322-own-loop-hand.md`:

      reserve two P3: P4:01,02; D2:31,32; D4:04,34;
      reserve two D2: P3:02,32; P4:41,42; D4:01,31.

  Since only one class is doubled, at least one of P3,D2 is a triple.

Now retain a 3,3,2,2 subpool in which this own-looped class remains
a triple. The common-corner 3,3,2,2 lemma in the same note applies:
it allows the asserted own loop to use any sources of the full pool.
Thus every 3,3,3,2 configuration assembles.

## 3. Five classes of sizes 3,3,3,1,1

Normalize the absent class to D_i. The present classes are

    A=P_i, B=P_j, C=P_k, E=D_j, F=D_k,

where {i,j,k}={2,3,4}. Their poles are 0i,0j,0k,1j,1k, and their
tricoloured corners are:

| Class | Corners |
| --- | --- |
| A | 01,0j,0k,i1,ij,ik |
| B | 01,0i,0k,j1,ji,jk |
| C | 01,0i,0j,k1,ki,kj |
| E | 01,0j,i1,ij,k1,kj |
| F | 01,0k,i1,ik,j1,jk |

Interchanging j,k leaves exactly six choices of the three triples:

    ABC, ABE, ABF, AEF, BCE, BEF.

The following small matching facts close these six cases.

### Own-loop matchings

Every row is used after two copies of its target class have been
reserved. The other source multiplicities are as in the specified
triple patterns.

| Looped class | When used | Six-corner completion |
| --- | --- | --- |
| A | Any pattern containing A as a triple | A:i1; E:ij; F:ik; B:0k; C:0j; any unused helper:01 |
| B | ABF or BEF | B:ji; F:j1,jk; A:0k; C:0i; E:01 |
| C | BCE | C:ki; E:k1,kj; A:0j; B:0i; F:01 |
| E | ABE or AEF | E:k1; C:kj; A:0j,ij; F:i1; B:01 |
| E | BCE | E:i1; A:ij; C:0j,k1,kj; B:01 |
| F | BEF | F:i1; A:ik; B:0k,j1,jk; C:01 |

The unused helper in the first row exists: the four helper classes
contain eight cubes in total, and only one from each has been used.
Every helper contains 01. All other rows use at most the stated
counts after the two target copies have been reserved.

### The six cases

**ABC.** The class A has an own loop. It therefore conflicts with
B and C, since all three pole pairs contain 0. The classes B,C also
conflict: after reserving one of each, complete a B target by

    B:ji,j1; F:jk; A:0k,01; C:0i.

Thus A requires three repeated colours and B,C require at least one
each, all distinct and all different from 0. Five colours would have
to fit into the four-element set {1,2,3,4}, a contradiction.

**ABE or AEF.** Both A and E have own loops. They conflict via a
B target. After reserving one A and one E, assign

    A:01,0k; C:0i; B:ji,

and fill j1,jk with two remaining B/F sources. This is possible
because B and F have combined multiplicity four, and only one B
has been used. Each remaining B/F source contains j1,jk.
The reserved classes can supply poles 0,j of B. The two triples
would require six different repeated colours, impossible.

**ABF.** Both A and B have own loops. Their poles intersect at 0,
so they conflict by restoration. Their two three-element repeated-
colour sets cannot be disjoint.

**BCE.** Both C and E have own loops. They conflict using a B
target: after reserving one C and one E, match

    B:ji,j1,jk; C:01,0i; A:0k.

The reserved C,E sources supply poles 0,j. Again the two triples
would need six different repeated colours.

**BEF.** Both B and F have own loops. They conflict using a C
target: after reserving one B and one F, match

    E:0j,k1,kj; B:01,0i; C:ki.

The reserved B,F sources supply poles 0,k. The same six-colour
contradiction applies.

All six triple placements are now covered. This proves the
3,3,3,1,1 case and hence the theorem.

## Scope

The reductions classify supports and the six ways to place three
triples on a five-class support. They do not enumerate physical-cube
inventories or assume any classification of fourteen-cube failures.
The proof is independent of the three-opposite target and may be
used in both of its multiplicity profiles.
