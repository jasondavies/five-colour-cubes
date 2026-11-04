# Pure fourteen-pools: the four-copy anchor, one-row cover

**Proved by hand.** Suppose every adjacent class has at most four copies,
the pool is all-adjacent and has fourteen cubes, and A=C(01) has four
copies. Suppose every other source either is disjoint from A in
tricoloured corners or meets A only in the row 0→{2,3,4}. Then the pool
has an assembly.

Here C(S) is the cut S→Sᶜ. Put Q={2,3,4}. Besides A the permitted classes
are

    P_i=C(0i), D_i=C(0,Q\{i}), Z_i=C(Q\{i})  (i∈Q),
    B=C(Q).

Write p_i,d_i,z_i,b for their counts and z=b+Σz_i for the total of the
classes disjoint from A. There are ten nonanchor copies. Each disjoint
class has at most three copies: four A and four copies of any such
class build an opposite target. Also z≤5, since six disjoint copies
with individual counts≤3 match the six tricoloured corners of C(Q),
and two A with the same repeat supply its bichromatic corners.

## 1. Two disjoint-from-A sources already force an opposite target

For q,s∈Q distinct, the opposite target with bipartition01|qs is supplied
by four A in one direction and four other sources at

    q→0, s→0, q→1, s→1.

The first two positions see only the z zero-intersection sources. Let
n_q count nonzero-intersection sources whose outset contains q. The
four-position Hall conditions reduce to

    z−z_q≥1, z−z_s≥1,
    z−z_q+n_q≥2, z−z_s+n_s≥2,
    z+n_q≥3, z+n_s≥3.

The union of all four neighbourhoods has size10−p_r≥6, where
Q={q,s,r}; every other required union follows from these inequalities.

If z≥3, choose q,s for which z−z_q,z−z_s≥2. At most one index can fail
this bound, because two counts z_i≥z−1 would sum to more than z. The
displayed conditions hold, giving an assembly.

Suppose z=2. Let Z be the subset of Q appearing in the two zero-source
outsets, and N the subset appearing in the eight nonzero-source
outsets. Both have at least two elements: each zero outset has two or
three Q-elements, and eight nonzero sources cannot all be the single
class P_i of capacity four. If |Z∩N|≥2, select q,s in the intersection
and again apply the displayed conditions.

The only remaining case is Z={q,s}, N={s,r}. The two zero sources are
both Z_r, while all eight nonzero sources lie in P_s,P_r,D_q.
The shared-four bounds p_s+d_q≤7 and p_r+d_q≤7 imply p_s,p_r≥1;
one of them is at least two. Assume p_s≥2. Build the opposite target
with bipartition{q,s}|{1,r}, omitting0:

    two Z_r: q→1,q→r;
    two P_s: s→1,s→r;
    two A:   1→q,1→s;
    one P_r: r→s;
    another P_r or D_q: r→q.

The last source exists because p_r+d_q=8−p_s≥4. Thus every failure
would have z≤1.

## 2. No P or D class can have four copies

First suppose d_i=4, with Q={i,j,k}. Four D_i and two A fill six
corners of the opposite target1i|jk; the remaining positions are i→j
and i→k. If two other cubes match these, we are done. Otherwise
p_i≤1, and if p_i=1 then d_j=d_k=0; if p_i=0, at most one of d_j,d_k
is positive.

There are at least five nonzero sources outside D_i. Hence p_j+p_k>0:
otherwise those sources are P_i,D_j,D_k, and the preceding restrictions
give at most four of them. At least four sources belong to
P_j,P_k,D_j,D_k; each fits at least one of

    j→1,j→i,k→1,k→i,

and a source in P_j or P_k fits two. Two distinct sources therefore
match two distinct positions in this four-set. Reserve a same-repeat
pair from D_i; its remaining two copies fill the other two positions.
One A fills0→i, and an unused nonzero source fills0→1. This completes
the D_i target, a contradiction.

Now suppose p_i=4. Reserve its same-repeat pair. Two A can fill0→j,0→k,
and the two remaining P_i can fill two of0→1,i→1,i→j,i→k. Every
other nonzero source fits0→1; if d_j+d_k>0, one of them also fits an
i-row corner, so two other sources complete the four-set. The same
holds if the unique zero source contains i. Thus failure forces
d_j=d_k=0 and, when z=1, the zero source is Z_i.

Use the opposite target1i|jk again. Two A and two P_i fill its forward
half. The reverse half has row capacities p_j,p_k and a universal
pool of size d_i+z. These sum to six. Its four positions can fail Hall
only if p_j+d_i+z≤1 or p_k+d_i+z≤1, which would force the other p-count
to be at least five. This is impossible. Consequently p_i,d_i≤3.

## 3. The remaining opposite-target Hall conditions

Ignore the zero source if present. There are N=10−z∈{9,10} nonzero
sources, in six classes of capacity three. For target1i|jk, two A fill
1→j,1→k. Label its six other positions

    a=i→j, b=i→k, c=j→1, d=j→i, e=k→1, f=k→i.

The six source neighbourhoods are

|Class|Positions|
|---|---|
|P_i|a,b|
|P_j|c,d|
|P_k|e,f|
|D_i|c,d,e,f|
|D_j|a,e|
|D_k|b,c|

All Hall inequalities are automatic from N≥9 and the capacity-three
bounds except

    p_i+d_j≥1, p_i+d_k≥1, p_j+d_i≥1, p_k+d_i≥1;
    p_i+d_j+d_k≥2, p_j+p_k+d_i≥2;
    p_j+d_i+d_k≥2, p_k+d_i+d_j≥2.                 (*)

Classifying the zero coordinates in these six counts gives a short
description if all three opposite targets fail:

**Family I.** The main positive classes are P_j,P_k,D_i, where
{i,j,k}=Q. Their counts are at least two and sum to at least eight.
There may be one additional main class of count one.

**Family II.** P_i,D_j,D_k each have count three, every other main
count is zero, and z=1.

Here are details of that classification. With zero or one zero
coordinate, some choice of i satisfies(*). With exactly two zeros,
the matched pair p_i=d_i=0 also allows target i, as do two zero
p-counts. If d_j=d_k=0, all targets can fail only when p_i=1,
giving Family I. If p_i=d_j=0 with i≠j, the third target k succeeds
unless d_k=1, again Family I. With at least three zeros, N≥9 and
the capacity-three bound force exactly three nonzero counts, all
three. Three P-counts, three D-counts, or a mixed triple whose
minority index matches one of the majority indices solve directly
by(*). The two unmatched mixed triples are exactly Families I,II.

## 4. Both families contradict repeated-colour pigeonhole

In Family I put U=P_j,V=P_k,W=D_i. Their three counts are at least
two, and at least two counts equal three. Any class here of size
three must use three distinct repeats in a failure. To see this,
reserve a same-repeat pair and use these tricoloured completions:

* U target: remaining U at j→k; two W at j→1,j→i; one V at0→1;
  two A at0→i,0→k.
* V target: the symmetric assignment.
* W target: remaining W at0→1; two U at j→1,j→i; two V at k→1,k→i;
  one A at0→i.

Moreover any two of U,V,W must use disjoint repeat sets. For U,V,
one cube from each repeating r supplies the bichromatic corners of
the U target; its tricoloured completion uses one further U, two W,
one further V and two A as above. For U,W, use their poles0 and1
to make an A target: three A fill1→i,1→j,1→k, while one further W,
one further U and one V fill0→i,0→k,0→j. The V,W case is symmetric.
Thus the two size-three classes demand six different repeated
colours, impossible in a five-colour palette.

In Family II let U=P_i,V=D_j,W=D_k. U must use three distinct repeats:
after reserving a repeated pair, two A fill0→j,0→k, one V fills i→j,
one W fills i→k, another V or W fills i→1, and the remaining U fills0→1.

The zero source contains at least one of j,k; assume it contains k.
Then V also must use three distinct repeats. After reserving a V pair,
the remaining V fills k→j, the zero source fills k→1, three U fill
0→1,i→1,i→j, and one A fills0→j. Finally U and V cannot share a
repeat: reserve one from each for an A target's bichromatic corners;
four A fill the three1-row corners and0→i, and the remaining two U
fill0→j,0→k. Again six different repeats would be required.

Every case gives an assembly, proving the one-row-cover lemma.

