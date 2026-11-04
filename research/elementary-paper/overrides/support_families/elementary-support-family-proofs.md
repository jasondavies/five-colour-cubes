# Elementary proofs for the two six-cut support families

The support-poset statement concerns arbitrary adjacent cuts. The butterfly
profile statement concerns fourteen adjacent cubes with class cap three. It is a conditional
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

A robust triple in a failure must use each of its three allowed repeats
once. If another source has pole pair Q meeting its pole pair P in one
colour, that source must repeat the colour in $P\setminus Q$. Otherwise
it shares an allowed repeat with a member of the triple, and the two
sources fill the robust target's bicoloured positions.

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

## 1. The common-corner support

For colours $a,b,i,j,k$, the six cuts containing $a\to b$ are
$C(ai),C(aj),C(ak),C(aij),C(aik),C(ajk)$.
Only this support description is needed from the common-corner alternative
here; its numerical assembly lemmas are proved separately.

## 2. Butterfly family: the coarse profile is forced

Use pivot colour `0`, and partition the other four colours into
`P={1,2}` and `Q={3,4}`. Assume every class has at most three copies. The six cuts are

    C_1: {0,1} -> {2,3,4},   C_2: {0,2} -> {1,3,4},
    C_3: {1,2,4} -> {0,3},   C_4: {1,2,3} -> {0,4},
    U:   {1,2} -> {0,3,4},   V:   {0,1,2} -> {3,4}.

Their counts are `x_1,x_2,x_3,x_4,u,v`. Define

    L = x_1+x_2+v,       R = x_3+x_4+u,       L+R=14.

The pole pair of `C_i` is `{0,i}`. Those of `U,V` are `P,Q`.
Each block contains three classes of capacity three. Thus $L,R\ge5$.

### Two completion criteria

**Low cuts are robust.** For U, the arcs $10,20$ have the common
source pool $C_3\cup C_4\cup U$, of size $R\ge5$. Each other arc's
pool omits at most two high classes and therefore has at least eight
sources. After any two reservations, a set confined to $10,20$ has
at least three neighbours, while a set meeting any other arc has at
least six. Hall proves robustness of U; the argument for V is symmetric.

**High cuts have a completion when their block weight is at least six.**
For C_1, after the two bicoloured reservations suppose at least two
C_1 copies remain. Use two for its private arcs $02,12$. The four
remaining arcs have pools

    03,04: C_1,C_2,V;
    13:    C_1,C_3,U,V;
    14:    C_1,C_4,U,V.

The first pool has size L; each singleton pool has at least
$14-3-3=8$ sources. Removing the four reserved copies leaves at
least two neighbours for a subset of $03,04$ when $L\ge6$,
and at least four for any subset meeting $13$ or $14$. Hall
completes the four positions. The other high cuts are symmetric.

### The low cuts are robust

Each block contains three classes of capacity three. Since $L+R=14$,
both block weights are at least five. The low-cut completion criterion
therefore makes both low cuts robust. In a failure, each uses every
repeated colour at most once.

### Both block weights are at least six

Suppose $L=5$. Then $R=9$, so $x_3=x_4=u=3$.
The robust low class U uses repeats $0,3,4$. Its repeat-restoration
constraint forces every C_1 source to repeat 2 and every C_2 source to
repeat 1. The high cuts C_3,C_4 have safe completion by their block
weight nine and the displayed high-cut criterion.
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

We have proved `L,R>=6`. Every high target
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

**Butterfly profile lemma.** A failing fourteen-pool in this family,
with every class of multiplicity at most three, has profile
$3,3,3,3,1,1$. No repeated-colour enumeration is needed for this statement.
