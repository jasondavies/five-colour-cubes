# Two opposites and thirteen adjacent cubes in a butterfly

4 November 2026

**Status: elementary proof; independent root audit passed.**

## Theorem

Take thirteen adjacent sources, with at most three in any one
tricoloured-corner class, supported in the butterfly

    A=C01, P=C02, L=C124, M=C123, U=C12, V=C012.

Adding any two opposite sources gives an eight-source five-colour
assembly. The proof uses only the common-corner-eleven lemma and
the explicit assignments below; it does not enumerate inventories.

Write their counts a,p,l,m,u,v. Each is at most three and their
sum is thirteen. An opposite source ab/cd contains both directions
of the four edges between the displayed pairs.

## 1. Four common-corner counts

The classes A,L,U,V all contain13; A,M,U,V all contain14;
P,L,U,V all contain23; and P,M,U,V all contain24. If one of
these four subpools has eleven sources, it assembles by
`../three_opposite_double/common-corner-eleven-hand.md`.

We may therefore assume

    a+l ≥3,  a+m ≥3,  p+l ≥3,  p+m ≥3.                (1)

For example, a+l≤2 would leave the common-corner24 subpool
P,M,U,V with at least eleven sources. The other three inequalities
follow in the same way.

The butterfly union misses exactly31,32,41,42. Every opposite
source contains at least one of these four corners. Indeed, if a
four-cycle avoided all four undirected edges between{1,2} and{3,4},
it would lie in the union of the triangles012 and034. A simple
cycle in this graph must lie in one of its triangle blocks, which
cannot contain a four-cycle.

## 2. All four high classes present

Suppose a,p,l,m are all positive. By(1), either a,p≥2 or l,m≥2:
otherwise one of a,p and one of l,m would both equal one,
contradicting the corresponding inequality. Also u+v≥1, since
the four high classes can contain at most twelve sources.

The permutation(1 3)(2 4), followed by reversing all directed
cuts, exchanges the two high pairs{A,P} and{L,M} and interchanges
U,V. Thus assume l,m≥2. Select one source K from U or V.
If an opposite O contains31, assemble target03/14 by

    O:31;  P:01;  L:40,43;  M:10,34;  A:04;  K:13.   (2)

Both low classes contain13. Interchanging1,2 and interchanging3,4
preserve the count hypotheses and act transitively on the four
missing corners. Consequently(2) covers every opposite source.
In this case even one of the two opposite sources suffices.

## 3. A high class absent

The butterfly symmetries act transitively on the four high classes,
so assume a=0. Equations(1) force l=m=3. The count equation gives

    p+u+v=7,  with 1≤p,u,v≤3.                        (3)

If either opposite O contains31, target03/14 has the assignment

    O:31;  P:01;  L:40,43;  M:10,34;  V:04;  U:13.  (4)

If an opposite contains41, interchange3,4. Thus we may suppose
both opposite sources avoid31 and41, equivalently avoid the
undirected edges13 and14.

There are exactly five such opposite varieties:

| Name | Opposite variety | Missing butterfly corners it supplies |
| --- | --- | --- |
| X | 02/34 | 32,42 |
| Y | 03/24 | 32 |
| Z | 04/23 | 42 |
| R | 02/14 | 42 |
| S | 02/13 | 32 |

To see completeness, if colour1 is omitted, the other four colours
have exactly their three pair partitions X,Y,Z. If colour1 is
present, its two neighbours must be0 and2. The other vertex in its
bipartition class is3 or4, giving S or R.

If the two opposite sources can supply32 and42 using different
sources, use target02/34. Assign those two corners to the opposite
sources,30 to M,40 to L, and03,04,23,24 to four P or V sources.
This is possible because p+v=7-u≥4, and both P and V contain
all four of these forward corners.

Consequently the only pairs left are two sources from{Y,S}, or
two from{Z,R}. Interchanging3,4 exchanges these alternatives.
Consider a pair from{Y,S}.

If at least one source is Y, assign it02, assign the other32,
and use target03/24 with

    Y:02;  other opposite:32;
    P:04;  M:34;  L:40,43,20;  U:23.                 (5)

Thus only two copies of S remain. If p≥2, target02/13 is

    S:12,32;  P:01,21;  M:10,30;  V:03;  U:23,      (6)

where the two S corners use the two distinct opposite sources.
Therefore the sole residual, up to the stated symmetries, is

    p=1; l=m=u=v=3; a=0; two copies of S=02/13.      (7)

Every reduction to(7) has followed from a count inequality, the
five geometrically determined opposite varieties, or an explicit
assembly. No search result is used.

## 4. Repeated colours close the sole residual

Recall that the pole pairs of M=C123 and V=C012 are04 and34,
respectively. A source of pole pair ab repeating colour r has
the two bicoloured corners(r,a) and(r,b).

The class M has an own loop: after reserving any two of its three
sources, match its six tricoloured corners by

    remaining M:34;  S:30;  P:24;  L:10,20;  U:14.  (8)

Likewise V has an own loop, with

    remaining V:04;  S:03;  P:24;  L:13,23;  M:14.  (9)

These assignments use only one opposite source each. If two M
sources repeated the same colour, reserve them for M's two
bicoloured target corners and use(8). The analogous construction
using(9) applies to V. Therefore, in a failing pool, the M triple
must use each repeat colour1,2,3 once, and the V triple each repeat
colour0,1,2 once.

Now choose the M source repeating1 for the bicoloured corner(1,0)
and the V source repeating1 for(1,4). Complete the M target by(8),
using an available M source at34. None of its other assignments
uses V, so all eight assigned sources are distinct. This is an
assembly, contradicting failure.

The theorem follows.

## Verification

`audit_butterfly_two_opposites.py` checks the butterfly symmetries,
the four common-corner families, the exact list of five avoiding
opposite varieties, every displayed fixed assignment, the two
low-class alternatives in(2), and the final repeated-colour
completion. It checks these geometric identities and source
counts only; it does not enumerate source inventories.
