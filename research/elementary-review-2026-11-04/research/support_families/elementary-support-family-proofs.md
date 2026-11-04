# Elementary proofs for the two six-cut support families

This note concerns fourteen adjacent-repeat cubes. It is a conditional
classification by **support family**, not a proof that every fourteen-cube
failure lies in one of these families. In particular, it does not yet rule out
a failure whose tricoloured-corner union supports an opposite-repeat target.

Use colours `0,1,2,3,4`. An adjacent class is a directed complete cut
`S -> S^c`, with `|S|=2` or `3`. Its poles are its two-element side, and the
three varieties in the class are distinguished by their repeated colour,
which is not a pole. A variety with poles `{p,q}` and repeated colour `r`
has bichromatic corners `(r,r,p)` and `(r,r,q)`.

A target cut is **robust** if its six tricoloured corners can still be
matched after any two source cubes are removed. Thus any two distinct
cubes supplying its two bichromatic corners complete a solution.

We use the established six-class lemma: a fourteen-cube failure has at
most five cubes in any adjacent class. We also use this elementary pair
bound: two classes with four common tricoloured corners have combined
count at most seven. For if their combined count is at least eight,
one class has at least four copies. Two copies of one of its three
varieties supply its bichromatic corners; two further copies supply its
two tricoloured corners outside the other class; four of the remaining
copies supply the four common corners.

Two useful consequences of robustness:

1. A robust class of size at least four solves, by the pigeonhole
   principle on its three varieties.
2. A robust class of size three in a failure has one copy of each of its
   three varieties. If another source has pole pair `Q` meeting its pole
   pair `P` in one colour, that source must repeat the colour in `P\Q`.
   Otherwise its repeated colour `r` is outside `P`; it and the `r`-copy
   in the robust class supply the target's two bichromatic corners.

## 0. Why there are only two support families

This reduction is also elementary; the enumeration of 4,231 labelled
posets is unnecessary.

For a collection of directed cuts, put `a <= b` when the arc `a -> b`
is absent from their union. Equivalently every source outset containing
`a` contains `b`. Including reflexive pairs makes this a preorder.
Break any equivalence class into a linear order. The resulting partial
order is weaker, so all source outsets remain upsets; its incomparability
graph is unchanged. An opposite-repeat target is corner-supported
exactly when this incomparability graph contains a four-cycle (not
necessarily induced).

Consider a partial order on five points whose incomparability graph
has no four-cycle. It contains, as a weaker order, one of these three:

* two points below two other points (`K_{2,2}`), with the fifth isolated;
* a diamond `x<y,z<w`, with the fifth isolated;
* a chain `x<y<z` together with `x<u` and `v<z`.

Here is a short completeness proof. If the height is at least four,
a four-chain contains the first order. If the height is three, choose
`x<y<z`, with remaining points `u,v`. Suppose neither the first order
nor a diamond occurs. Neither `u` nor `v` is comparable with `y`, since
such a comparison gives two points below two others. Each can be above
`x` or below `z`, but not both, which would give a diamond. Avoiding
an incomparability four-cycle between `{x,y}` and `{u,v}` forces one
of `u,v` above `x`; avoiding one between `{y,z}` and `{u,v}` forces
one below `z`. They are different, giving the third order.

If the height is at most two, split the points into nonisolated minima,
nonisolated maxima, and isolated points. An antichain has size at most
three, so these class sizes are `(2,2,1)`, `(2,3,0)`, or `(3,2,0)`.
In the first case every minimum must be below every maximum: a missing
comparison `a<z`, together with the other minimum and the isolated
point, gives an incomparability four-cycle. In the `(2,3,0)` case each
minimum has at least two upper neighbours; otherwise it and the third
maximum are incomparable with the other two maxima. Two different
two-element upper neighbourhoods also give an incomparability
four-cycle. Thus the minima have two common upper neighbours, giving
the first order. The last case is dual.

The size-two and size-three upsets of the first order are exactly the
six butterfly cuts of Section 2. For a diamond, every such upset
contains its top and omits its bottom; conversely every size-two or
size-three subset with these properties is an upset. The same is true
for the third order: containing `x` would require four points, and
omitting `z` would leave at most one. Thus both of the latter orders
give exactly the six common-corner cuts of Section 1.

Consequently every all-adjacent collection whose corner union supports
no opposite-repeat target lies in one of the two support families below.

## 1. Common-corner family: no failure of size fourteen

Let the colours be `a,b,1,2,3`. The six cuts containing the common arc
`a -> b` are

* `A_i = {a,i} -> {b,j,k}`;
* `B_i = {a,j,k} -> {b,i}`,

where `{i,j,k}={1,2,3}`. Write their counts as `a_i,b_i`.
Each count is at most five, their sum is fourteen, and

    a_i + b_j <= 7  whenever i != j.                 (1)

Indeed these pairs of cuts have four common arcs.

The six arcs of `A_i` have source-class neighbourhoods

| Arc | Source classes |
| --- | --- |
| `a -> b` | all six |
| `a -> j` | `A_i,A_k,B_j` |
| `a -> k` | `A_i,A_j,B_k` |
| `i -> b` | `A_i,B_j,B_k` |
| `i -> j` | `A_i,B_j` |
| `i -> k` | `A_i,B_k` |

Hall's inequalities after arbitrary removal of two cubes reduce to

    total >= 8;
    a_i+b_j >= 3, a_i+b_k >= 3;
    a_i+b_j+b_k >= 5;
    a_i+a_j+b_k >= 4, a_i+a_k+b_j >= 4;
    a_i+a_j+b_j+b_k >= 6, a_i+a_k+b_j+b_k >= 6;
    total-b_i >= 7.                                (2)

These follow directly by taking unions of the neighbourhoods in the table;
all other Hall inequalities are implied by these. Interchanging `A` and
`B` gives the conditions for `B_i`.

### A class of size at least four gives a solution

If `a_i=5`, every condition in (2) is automatic except possibly one of

    a_j+b_j+b_k >= 1,  a_k+b_j+b_k >= 1.

If the first fails, only `A_i,A_k,B_i` remain, and their total is at most
`5+7=12` by (1). The second is symmetric. Thus every class of size five
is robust.

Suppose the maximum class size is four and `a_i=4`. The only possible
failures of (2) are

    b_j+b_k=0,

or `b_j+b_k=1` together with `a_j=0` or `a_k=0`. In the latter case the
total is at most `4+4+4+1=13`, impossible. In the former case

    a_j+a_k+b_i=10.

All three numbers are at most four, so at least one is four. If `b_i=4`,
then `B_i` is robust because its two opposite neighbours total at least
six. If, say, `a_j=4`, then `b_i>=2` and (2) makes `A_j` robust.

Consequently a failure has every class size at most three.

### The remaining small classes are incompatible

If all counts are at most three and the total is fourteen, every class
of size three satisfies (2): its two opposite neighbours total at least
two, and the other inequalities follow immediately from the total.
At least two classes have size three.

Two robust size-three classes cannot have intersecting pole pairs:
consequence 2 above would force all three copies of one to have the same
repeated colour, although robustness forces its three repeated colours
to be distinct. As there are only five colours, at most two pole pairs
can be disjoint. Hence there are exactly two size-three classes with
disjoint pole pairs, and the other four counts are all two.

The disjoint pair must be `A_i,B_j` with `i!=j`. The class `A_j`, which
has positive count, shares pole `a` with `A_i` and pole `j` with `B_j`.
Consequence 2 forces it to repeat both `i` and `b`, a contradiction.

**Theorem 1.** Fourteen adjacent-repeat cubes whose classes all contain
one common directed corner always solve.

## 2. Butterfly family: the coarse profile is forced

Use pivot colour `0`, and partition the other four colours into
`P={1,2}` and `Q={3,4}`. The six cuts are

    C_1: {0,1} -> {2,3,4},   C_2: {0,2} -> {1,3,4},
    C_3: {1,2,4} -> {0,3},   C_4: {1,2,3} -> {0,4},
    U:   {1,2} -> {0,3,4},   V:   {0,1,2} -> {3,4}.

Their counts are `x_1,x_2,x_3,x_4,u,v`. Define

    L = x_1+x_2+v,       R = x_3+x_4+u,       L+R=14.

The pole pair of `C_i` is `{0,i}`. Those of `U,V` are `P,Q`.
The shared-four pair bounds include

    x_1+v<=7, x_2+v<=7, x_3+u<=7, x_4+u<=7, u+v<=7. (3)

### Two elementary completion observations

**Low cuts.** Under total fourteen and individual counts at most five,
`U` is robust exactly when `R>=4`, and `V` exactly when `L>=4`.
For `U`, its arcs `1->0,2->0` have the same source pool `C_3,C_4,U`.
Each of its four remaining arcs has a source pool omitting just two
high classes, hence at least four sources. The union of the pools of
any two distinct remaining arcs omits at most one high class and has
at least nine sources. The union of the first pool and any remaining
arc's pool also omits at most one high class. These observations verify
Hall after arbitrary deletion of two sources. The pair `1->0,2->0`
also proves necessity of `R>=4`. The argument for `V` is symmetric.

**High cuts.** The cut `C_1` has two private arcs `0->2,1->2`, supplied
only by `C_1`. After two bichromatic-source reservations leaving at
least two `C_1` copies, reserve two such copies for these private arcs.
Its other four arcs have source pools

    0->3,0->4: C_1,C_2,V;
    1->3:      C_1,C_3,U,V;
    1->4:      C_1,C_4,U,V.

They can always be matched if

    L>=6,   14-x_2-x_3>=5,   14-x_2-x_4>=5.         (4)

To see this, the identical first pool still has at least two sources,
each singleton pool at least one, and any other union has at least
`14-5-4=5` sources after the four reservations. In particular `C_1`
is robust if `x_1>=4` and (4) holds. Conversely these are precisely
the nonautomatic robust Hall inequalities. Symmetric statements hold
for the other three high cuts.

### The low cuts are robust and their repeats are distinct

Suppose `R<=3`, hence `L>=11`. If `x_1,x_2<=3`, inequalities (3) give
`L<=10`: for `v<=4` this is immediate, and if `v=5`, both high counts
are at most two. Thus one of `x_1,x_2` is at least four. It is robust:
`L>=11`, while the two high counts on the other side are at most three,
so the other inequalities in (4) hold. This gives a solution.

The symmetric case is identical. A failure therefore has `L,R>=4`,
both low cuts are robust, `u,v<=3`, and each low cut uses each repeated
colour at most once.

### All high counts are at most three

Suppose `x_1>=4`. If `L>=6`, (4) can fail only if
`x_2=x_3=5` or `x_2=x_4=5`. Total fourteen then forces `x_1=4` and
all other counts zero; in either case `C_2` is robust. Thus a failure
must have `L<=5` and `R>=9`.

If `x_3>=4`, it is robust unless
`x_3+x_2+u+v<5`, since its other cross-pool includes `x_1>=4`.
The exception forces `x_3=4` and `x_2=u=v=0`. Then `R>=9` forces
`x_4=5`, and `C_4` is robust. Thus `x_3,x_4<=3`.
As also `u<=3`, we must have

    R=9,   x_3=x_4=u=3,   L=5.                     (5)

The robust size-three low class `U` has repeated colours `0,3,4`.
Its bichromatic corners force every `C_1` copy to repeat `2`, and
every `C_2` copy to repeat `1`. The completion observation applies
to `C_3,C_4` (their side has weight nine).

If `C_3` or `C_4` has a copy repeating `2`, it pairs with a `C_1`
copy to supply that high target's bichromatic corners, giving a solution.
So `C_3` uses only repeats `1,4`, and `C_4` only `1,3`.
If both use repeat `1`, the robust target `V` with repeat `1` solves.
Otherwise `C_3` consists entirely of repeat `4`, or `C_4` entirely
of repeat `3`.

In the first case build the target of class `C_1` with repeat `4`:
use the repeat-`4` copy of `U` for bichromatic corner `(4,4,1)` and
a `C_3` copy for `(4,4,0)`; four `C_1` copies supply its private arcs
and `0->3,0->4`; the two unused `U` copies supply `1->3,1->4`.
The second case is identical with `3` in place of `4`.
This contradicts failure. Every high count is at most three.

### Both block weights are at least six

Now all six counts are at most three, so `L,R>=5`. Suppose `L=5`.
Then (5) again holds, with `x_1,x_2<=3`. As before `C_1` repeats only
`2`, `C_2` only `1`, and the high cuts `C_3,C_4` have safe completion.
No repeated colour can occur in both `C_3,C_4`, nor in one of them
and a positive `C_1` or `C_2`: the two corresponding cubes would
supply a high target's bichromatic corners, leaving two private copies.

If one of `x_1,x_2` is at least two, any repeat `4` in `C_3` or repeat
`3` in `C_4` gives a solution in that positive high class. Reserve
that copy and the corresponding copy of `U` for the bichromatic corners;
use two copies of the chosen high class for its private arcs; use
two of the remaining `L-2=3` sources in `C_1,C_2,V` for `0->3,0->4`;
and use the two remaining `U` copies for its other two arcs.
Avoiding this forces `C_3,C_4` to use only repeats `1,2`; their repeat
sets are disjoint and nonempty, so one uses only `1` and the other only
`2`. Either positive class on the other side then shares a repeat with
one of them and gives a solution.

The only remaining possibility is `x_1=x_2=1,v=3`. Now `V` has repeats
`0,1,2`; its repeat-`1` copy and the `C_2` copy provide the bichromatic
corners of the `C_3` target with repeat `1`, which has safe completion.
Thus `L=5` is impossible, and symmetrically so is `R=5`.

We have proved `L,R>=6`. Because all high counts are at most three,
the remaining conditions in (4) are automatic. Every high target
therefore has safe completion whenever two copies remain for its
private arcs.

### Repeated-colour counting forces the profile

If a nonpivot colour `q` occurs as a repeat in `U`, robustness of `U`
forbids that repeat in `C_1,C_2`. Also `x_1+x_2=L-v>=3`, so one of
these high classes has at least two copies. Any high-class copy
repeating `q` could pair with the `U` copy to provide that target's
bichromatic corners, with safe completion. Therefore `q` is absent
from **all** high classes. Symmetrically, any nonpivot repeat in `V`
is absent from all high classes.

Furthermore a repeated colour used by a high class of size three
cannot occur in another high class: one copy from each would supply
the size-three class's bichromatic corners, leaving two private copies.

Let `k` be the number of colours still available as high-class repeats.
If `1<=k<=3`, the total `H=x_1+x_2+x_3+x_4` is at most `k+7`.
Indeed, if `t` high classes have size three, they use disjoint nonempty
repeat sets, so `t<=k`. If `t<=k-1`, then `H<=3t+2(4-t)<=k+7`.
If `t=k`, every other high class is empty, so `H=3k<=k+7`.
If `k=0`, then `H=0`.

Suppose one low class has at least two copies. If both low classes
are nonempty, their distinct repeats exclude at least `u+v-2`
nonpivot colours, so `k<=6-u-v<=3`. The bound gives

    H <= 13-u-v < 14-u-v = H,

a contradiction (and `k=0` is immediate). If one low class is empty,
say `v=0,u>=2`, then `k<=5-u<=3`, giving the even stronger
`H<=12-u<14-u`. Thus `u,v<=1`.

Finally `H<=12` and total fourteen force

    (x_1,x_2,x_3,x_4,u,v) = (3,3,3,3,1,1).

**Theorem 2.** A fourteen-cube failure supported in the butterfly family
has exactly this coarse profile. In particular its invariant is
`W=3*(4*binom(3,2))=36`.

Combining this with the separate repeated-colour refinement argument
gives the nine derangements in each butterfly configuration, hence
`30*9=270` labelled failures in this support branch.

## Remaining global step

The support-poset reduction says that an all-adjacent pool whose corner
union contains no opposite-repeat target is supported in one of the
two families above. Thus these arguments completely settle that branch
by hand. What is still missing is a proof that a fourteen-cube
all-adjacent failure cannot have a corner-supported opposite target.
The weaker assertion that such a target itself must solve is false;
a proof must be allowed to switch to an adjacent target.
