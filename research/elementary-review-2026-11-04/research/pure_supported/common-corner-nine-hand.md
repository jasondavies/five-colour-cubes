# Nine cubes occupying all six classes through one corner

**Theorem.** Suppose all six adjacent tricoloured classes containing a
fixed directed corner occur. Any nine cubes from those classes have an
assembly. Two useful eight-cube configurations also always assemble.

This is a hand proof. It uses only repeated-colour pigeonhole and the
explicit six-corner matchings below.

Normalize the common directed corner to `01`. Put `Q={i,j,k}={2,3,4}`
and write

\[
P_i=C(0i),\qquad D_i=C(0,Q\setminus\{i\}).
\]

Their pole pairs are respectively `0i` and `1i`. These six cuts all
contain `01`. Simultaneous cut reversal and interchange of 0 and 1
interchanges the `P` and `D` families.

Call a class looped when two copies with the same repeated colour
can provide bicoloured corners and the remaining sources match its
six tricoloured corners. Call two classes joined when copies with the
same repeated colour can do the analogous job. In a failure, a looped
class uses different repeated colours on all its copies; joined
classes have disjoint repeated-colour sets.

We use one elementary observation. If class `U` has an own-orientation
loop, it is joined to every present class `V` whose pole pair meets
its pole pair. Reserve one `U,V` for an `U` target's bicoloured
corners. Compared with the loop matching, a `U` copy is restored and
one `V` is removed; the restored universal `U` replaces that `V` if
it had been used in the six-corner matching.

## 1. A triple and five singletons already solve

Take three `P_i` and one copy of each other class. The class `P_i`
has a loop, as witnessed after reserving two copies by

\[
P_i:i1,\quad P_j:0k,\quad P_k:0j,\quad
D_i:01,\quad D_j:ij,\quad D_k:ik.
\]

The four classes `P_i,P_j,D_j,D_k` are pairwise joined:

* `P_i,P_j` are joined by the own-loop observation.
* For `P_i,D_j`, use target `P_j`: after reserving one of each,
  use remaining `P_i:01,0k`, `P_k:0i`, `D_i:ji`, `D_k:jk`,
  and `P_j:j1`. The `P_i,D_k` case is symmetric.
* Any two of `P_j,D_j,D_k` can supply the poles `1j` of target
  `D_j`. The three `P_i` fill `0j,i1,ij`, while `P_k` fills `kj`,
  `D_i` fills `k1`, and the unused member of that three-class group
  fills `01`.

Thus `P_i` requires three distinct repeats, and each of the other
three joined classes requires another repeat. Six different colours
would be needed. This proves the eight-cube statement with class
counts `3,1,1,1,1,1`. By symmetry a triple in any of the six classes
works.

## 2. Two opposite-index doubles and four singletons solve

Take two `P_i`, two `D_j` with `i!=j`, and one of each other class.
Both doubled classes have own loops:

| Reserved class | Six-corner completion |
|---|---|
| two `P_i` | `P_j:0k`; `P_k:0j`; `D_i:01`; `D_j:i1,ij`; `D_k:ik` |
| two `D_j` | `P_i:0j,ij`; `P_k:kj`; `D_i:k1`; `D_k:i1`; `P_j:01` |

The classes `P_i,D_j,P_j,D_i` form a conflict clique. Four of its
edges follow from the own-loop observation: `P_i` meets the poles of
`P_j,D_i`, and `D_j` meets those of `P_j,D_i`. The remaining two
edges have these direct completions after reserving the indicated
pair:

| Reserved pair | Target | Six-corner completion |
|---|---|---|
| `P_i,D_j` | `P_j` | remaining `P_i:0k`; `P_k:0i`; `D_i:ji`; `D_k:jk`; remaining `D_j:01`; `P_j:j1` |
| `P_j,D_i` | `P_i` | `P_i:01,0k`; `P_k:0j`; `D_j:i1,ij`; `D_k:ik` |

The two looped classes require two repeats each, and the other two
classes require one each. Again six different colours would be needed.

## 3. Three doubles in one family and three singletons solve

Take two of each `P_i,P_j,P_k` and one of each `D_i,D_j,D_k`.
All six classes are pairwise joined. Up to permutations of `i,j,k`,
there are four kinds of pair; these completions cover all of them.

| Reserved pair | Target | Six-corner completion |
|---|---|---|
| `P_i,P_j` | `P_i` | remaining `P_i:i1`; remaining `P_j:0k`; `P_k:0j`; `D_i:01`; `D_j:ij`; `D_k:ik` |
| `P_i,D_i` | `P_i` | remaining `P_i:i1`; `D_j:ij`; `D_k:ik`; `P_j:0k,01`; `P_k:0j` |
| `P_i,D_j` (`i!=j`) | `P_j` | `P_j:j1`; `D_i:ji`; `D_k:jk`; remaining `P_i:0k`; `P_k:0i,01` |
| `D_i,D_j` | `D_i` | `D_k:j1`; `P_j:0i,ji`; `P_k:k1,ki`; `P_i:01` |

Six pairwise disjoint nonempty repeated-colour sets cannot fit into
five colours. Interchanging the `P` and `D` families gives the
symmetric case with three doubled `D` classes.

## 4. Deduction for any nine cubes

If any class has at least three copies, Section 1 applies. Otherwise
each class has one or two copies, and at least three classes are doubled.
If doubles occur in both families, there is an opposite-index doubled
pair `P_i,D_j` with `i!=j`: with at least three doubled classes, not all
cross-family pairs can share the same index. Section 2 applies.
If all doubles are in one family, all three classes of that family
are doubled, and Section 3 applies.

Thus nine cubes occupying all six common-corner classes always solve.
