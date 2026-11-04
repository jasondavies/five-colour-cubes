# A weaker numerical target sufficient for N5=15

Let g_j be the adjacent tricolour-class multiplicities and o the total
number of opposite-repeat cubes. Put

    A=sum_j binom(g_j,2),   W=3A-4binom(o,2).

The desired identity W=36 for every failing fourteen-cube pool is stronger
than necessary. The following conditional result is elementary.

**Proposition.** If every failing fourteen-cube pool satisfies31<=W<=38,
then no fifteen-cube pool fails.

**Proof.** Suppose a fifteen-cube pool fails. Every one-cube deletion also
fails. Write W for the fifteen-cube statistic. Deleting an opposite cube
gives W+4(o-1); deleting an adjacent cube from a class of size g gives
W-3(g-1).

If both types occur, subtracting these two deletion values yields

    4(o-1)+3(g-1)<=7.

Thus o<=2.

If o=1, W itself lies in[31,38] and is divisible by3, hence W=33 or36.
The adjacent deletion bounds force every g<=2 (indeed g=1 if W=33).
There are fourteen adjacent copies, so A<=7 and W<=21, a contradiction.

If o=2, opposite deletion gives W<=34, while adjacent deletion gives
W>=31. Since W=3A-4 is2mod3, W=32. Now every adjacent deletion forces
g=1, so A=0 and W=-4, again a contradiction.

The all-opposite case gives negative deletion values and is impossible.
It remains to consider o=0. For each nonzero class g,

    3(A-g+1) in[31,38],

so A-g+1 is11 or12. Set k=A-11. Every nonzero g is k or k+1.
Using sum g=15 gives

    15(k-1)<=sum g(g-1)=2A=2k+22<=15k.

Hence k=2. Therefore A=13 and all nonzero classes have size2 or3.
If there are a classes of size2 and b classes of size3, then

    2a+3b=15,   a+3b=13.

Subtracting gives a=2 and then3b=11, impossible. QED.

## The interval cannot be widened by this purely numerical argument

* Allowing30 admits the fifteen-copy adjacent profile(4,3,2,2,2,2):
  its fourteen-copy deletions have W=30,33,36.
* Allowing39 admits profile(3,3,3,3,3): every deletion has W=39.

Thus[31,38] is the widest integer interval containing36 for which the
deletion-profile argument can work without further geometric input.
The geometric bound31<=W<=38 remains unproved; the proposition is not
an unconditional proof of N5=15.
