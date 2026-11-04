# A common-corner 3,2,2,2,1 core always assembles

**Lemma.** Suppose five distinct adjacent tricoloured classes containing
one common directed corner occur with multiplicities `3,2,2,2,1`.
These ten sources always admit an assembly, irrespective of their
repeated colours.

The proof consists of elementary six-corner completions and
repeated-colour pigeonhole arguments. It does not use a classification
of failed pools.

## 1. Notation and the five-class normal form

Normalize the common corner to `01`, write `Q={i,j,k}={2,3,4}`, and set

\[
P_i=C(0i),\qquad D_i=C(\{0\}\cup(Q\setminus\{i\})).
\]

Their pole pairs are `0i` and `1i`, respectively. Reversing every cut
and interchanging 0 and 1 exchanges the P and D families. We may
therefore suppose the absent class is `D_i`. The present classes and
their corners are

| Class | Corners |
|---|---|
| `P_i` | `01,0j,0k,i1,ij,ik` |
| `P_j` | `01,0i,0k,j1,ji,jk` |
| `P_k` | `01,0i,0j,k1,ki,kj` |
| `D_j` | `01,0j,i1,ij,k1,kj` |
| `D_k` | `01,0k,i1,ik,j1,jk` |

Write their multiplicities as `a,b,c,e,f`, respectively. Thus these
five positive numbers, in some order, are `3,2,2,2,1`.

An **own loop** means that, after reserving two copies of a class,
the other sources match all six corners of that class. In a failure,
a looped class must use a different repeated colour on every copy.
Two classes **conflict** if reserving one copy of each permits a
six-corner completion of a target whose two poles they can supply.
Conflicting classes must have disjoint repeated-colour sets.

We use the universal-restoration observation: a class with an own
loop conflicts with every present class whose pole pair meets its
own. Restore one reserved copy of the looped class and remove the
other class's reserved copy; the restored universal source replaces
that removed source if the six-corner matching had used it.

## 2. Four useful loop completions

The following facts follow directly from the corner table.

1. **If `a>=2`, then `P_i` has an own loop.** After reserving two
   `P_i`, use `P_j:0k`, `P_k:0j`, and an additional `P_j` or `P_k`
   at `01`. Such an additional copy exists because `b+c>=3`.
   Use `D_j:ij`, `D_k:ik`, and one remaining source from
   `D_j,D_k,P_i` at `i1`. There are enough because
   `e+f+a-2>=3`.
2. **If `b=3` and `f>=2`, then `P_j` has an own loop.** After the
   reservation, match
   `P_j:ji; D_k:j1,jk; P_i:0k; P_k:0i; D_j:01`.
3. **If `e=3`, then `D_j` has an own loop.** After the reservation,
   use `D_j:k1; P_i:ij; P_k:kj; D_k:i1; P_j:01`, and one additional
   `P_i` or `P_k` at `0j`. The last copy exists because `a+c>=3`.
4. **If `e=2` and `a=c=2`, then `D_j` has an own loop.** Use
   `P_i:0j,ij; P_k:k1,kj; D_k:i1; P_j:01` after reserving the two
   `D_j`.

We now locate the unique triple. Interchanging `j,k` leaves three
possibilities: `P_i`, `P_j`, or `D_j`.

## 3. The triple is `P_i`

The four classes `P_i,P_j,D_j,D_k` form a conflict clique.

The edge `P_i,P_j` follows from the own loop of `P_i`.
For the edge `P_i,D_j`, use target `P_j`. After reserving one of
each, the two remaining `P_i` fill `01,0k`, and `P_k` fills `0i`.
The three other target corners `j1,ji,jk` are filled by `P_j,D_k`:
use a `P_j` at `ji`, then two remaining copies at `j1,jk`.
There are at least three copies altogether because `b+f>=3`.
The edge `P_i,D_k` is symmetric.

For any pair among `P_j,D_j,D_k`, use target `D_j`: the reserved
pair can supply its poles `1j`. The three `P_i` fill `0j,i1,ij`.
Two sources from `P_k` and the unreserved `D_j` fill `k1,kj`.
At least two are available since `c+e>=3` and at most one `D_j`
was reserved. Any still unused source fills `01`; at this point
only seven of the ten sources have been reserved or used.

The looped triple needs three distinct repeated colours, and each
other member of the four-class clique needs another colour. Six
different colours would be required, which is impossible.

## 4. The triple is `P_j`

First suppose the singleton is `P_k` or `D_j`. Then `a=f=2`, so
`P_i` and `P_j` both have own loops. They conflict because their
pole pairs share 0. Their five required repeated colours would all
have to avoid 0, an impossibility.

If the singleton is `P_i`, then `c=e=f=2`. The looped triple
`P_j` conflicts with both `P_i,P_k`. These latter two also conflict:
reserve one of each and complete target `P_i` by

\[
D_j:i1,ij;\quad D_k:0k,ik;\quad
\text{remaining }P_k:0j;\quad P_j:01.
\]

The three classes need at least five different repeated colours,
all avoiding their common pole 0. This is impossible.

It remains that the singleton is `D_k`, so `a=c=e=2`. Both `P_i`
and `D_j` have own loops. The four classes `P_i,P_j,P_k,D_j` form
a conflict clique. Own-loop restoration gives the edges
`P_i,P_j`, `P_i,P_k`, and `D_j,P_j`. The other edges are witnessed
by the following completions, made after reserving the indicated pair.

| Reserved pair | Target | Six-corner completion |
|---|---|---|
| `P_i,D_j` | `P_j` | remaining `P_i:0k`; `P_k:0i`; remaining `D_j:01`; `P_j:ji,j1`; `D_k:jk` |
| `P_k,D_j` | `P_j` | `P_j:j1,ji,jk`; `P_i:01,0k`; remaining `P_k:0i` |
| `P_j,P_k` | `P_j` | remaining `P_j:ji,j1`; `D_k:jk`; `P_i:01,0k`; remaining `P_k:0i` |

The two looped doubles and the other two nonempty classes would
require `2+2+1+1=6` distinct repeated colours. This is impossible.

## 5. The triple is `D_j`

If `P_i` is not the singleton, then `a=2`. Thus `P_i` and `D_j`
are looped and both conflict with `P_j`. They also conflict with
one another. To see this, reserve one of each for target `P_j`.
Use remaining `P_i:0k`, `P_k:0i`, and remaining `D_j:01`.
The classes `P_j,D_k` fill the other three corners `ji,j1,jk`,
using `P_j` for `ji`; there are enough copies because `b+f>=3`.
This three-class clique would require `2+3+1=6` distinct repeats.

Finally let `P_i` be the singleton, so `b=c=f=2`. We show that
`D_j,P_i,P_j,P_k` form a clique. The edge `D_j,P_j` follows
from the own loop of `D_j`. The other five edges have these
completions.

| Reserved pair | Target | Six-corner completion |
|---|---|---|
| `P_i,P_j` | `P_i` | `D_j:0j,i1,ij`; `D_k:0k,ik`; `P_k:01` |
| `P_i,P_k` | `P_i` | `D_j:0j,i1,ij`; `D_k:0k,ik`; `P_j:01` |
| `P_j,P_k` | `P_j` | remaining `P_j:ji`; `D_k:j1,jk`; `P_i:0k`; remaining `P_k:0i`; `D_j:01` |
| `P_i,D_j` | `P_j` | `P_j:ji,j1`; `D_k:jk,0k`; `P_k:0i`; remaining `D_j:01` |
| `P_k,D_j` | `P_j` | `P_j:ji,j1`; `D_k:jk`; `P_i:0k`; remaining `P_k:0i`; remaining `D_j:01` |

The looped triple and the three other nonempty classes require
`3+1+1+1=6` distinct repeated colours. This final contradiction
proves the lemma.
