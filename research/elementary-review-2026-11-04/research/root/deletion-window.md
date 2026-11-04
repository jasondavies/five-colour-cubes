# A weaker invariant would suffice

For a collection let g_j be the twenty adjacent-class multiplicities and
o its total number of opposite-repeat cubes. Define

    A = Σ_j binom(g_j,2),   B = binom(o,2),   W = 3A−4B.

The conjectured identity W=36 for every fourteen-cube failure would imply
N₅≤15: every pair in a hypothetical fifteen-failure survives thirteen of
its fifteen one-cube deletions, so

    13 W₁₅ = 15·36 = 540,

which is impossible because W₁₅ is an integer.

The exact identity is stronger than necessary.

**Proposition.** It is enough to prove 31≤W≤38 for every fourteen-cube
failure.

**Proof.** Let a fifteen-failure have value w and opposite count o.
Deleting an adjacent cube from a class of size g gives

    w−3(g−1),

while deleting an opposite cube gives

    w+4(o−1).

All these values would belong to [31,38]. If both kinds occur, comparison
gives 4(o−1)+3(g−1)≤7 and hence o≤2.

If o=1, w=3A belongs to [31,38], so w=33 or36. The adjacent-deletion
lower bound forces every g≤2. The fourteen adjacent cubes then have
A≤7, contradicting w≥31.

If o=2, the opposite deletion gives w≤34 and an adjacent deletion gives
w≥31. Since w=3A−4, necessarily w=32. Now w−3(g−1)≥31 forces every
g≤1, making A=0, a contradiction. An all-opposite pool has negative W,
so that case is impossible too.

It remains that o=0. Write A=Σ binom(g,2). Each deletion value
3(A−g+1) is either33 or36. Thus every positive g equals k or k+1,
where k=A−11. Since Σg=15,

    15(k−1)/2 ≤ A=k+11 ≤ 15k/2.

These inequalities force k=2. Hence every class has size two or three.
If x,y count the classes of those sizes, then

    2x+3y=15,   x+3y=A=13.

Consequently x=2 and 3y=11, impossible. This proves the proposition.

The interval cannot be enlarged by one at either endpoint using this
numerical argument alone. The adjacent-only fifteen-profile
(4,3,2,2,2,2) has deletion values30,33,36, while the profile
(3,3,3,3,3) has every deletion value39. These are numerical profiles,
not claims of geometrically failing inventories.

**Unproved geometric step:** neither the global lower bound31 nor the
global upper bound38 is established by this note.

