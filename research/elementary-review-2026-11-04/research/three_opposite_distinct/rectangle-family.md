# Three distinct high opposite sources and a one-sided rectangle family

4 November 2026

**Status: elementary proof; independent root audit passed.**

**Lemma.** Suppose three distinct opposite varieties each meet at
least two underlying edges of T=01|23. Suppose eleven adjacent
sources, with class cap three, have all their T-corners in the
forward half 01→23. Then the pool assembles a five-colour target.

The union of the opposite sources need not cover all edges of T.
This stronger scope is useful for the unsupported common-target
case as well.

The six possible adjacent classes are

    A=C(01), B=C(014),
    P=C(04), Q=C(14), R=C(012), S=C(013).

Write their counts as a,b,p,q,r,s. Their sum is eleven and each
count is at most three. The list follows directly by intersecting
each cut with the square T, or by choosing the side of the fifth
colour after prescribing the four square vertices.

We use two previously proved lemmas:

- `global-zero-edge.md`: three distinct opposite sources and eleven
  capped adjacent sources avoiding an underlying edge assemble;
- `../three_opposite_double/common-corner-eleven-hand.md`: eleven
  capped adjacent sources sharing one directed corner assemble.

## 1. Only three or four peripheral classes need consideration

Only P,Q contain the underlying edge 01, and only R,S contain 23.
If either pair of classes is absent, the global-zero-edge lemma
applies. Thus at least one class from each pair occurs.

If there is just one from each pair, all occupied classes share a
directed corner of T. For example A,B,P,R all contain03; the other
choices are obtained by interchanging 0,1 or 2,3. The common-corner
lemma applies.

It remains that three or four of P,Q,R,S occur. The symmetries
interchanging 0,1, interchanging 2,3, and reversing all directions
while exchanging the two parts of T allow the three-class case
to be normalized to p,q,r>0 and s=0.

## 2. All four peripheral classes occur

Partition the four edges of T into the two disjoint pairs

    E={02,13}, F={03,12}.

Three distinct high opposite varieties collectively cover at least
three edges of T: a fixed two-edge intersection determines its
opposite variety uniquely, and the variety T itself covers all four.
Hence at least one of E,F is entirely supported by the three sources.

Any two target edges have at least two opposite-source neighbours,
since at most one of the three distinct high varieties can have
its whole intersection in the complementary pair. Therefore two
opposite cubes can fill the two reverse directions on the supported
pair. Use E, say, so these positions are20,31, and take target

    U={01,02,13,23}.

Put P at01, Q at10, R at23, and S at32. The only positions left
are02,13. Every one of the seven remaining adjacent sources meets
this pair: A,B meet both; P,S meet02; Q,R meet13. At least three
remaining sources meet each position. Indeed at most six sources
belong to the two classes missing that position, and at most two
supporting sources have just been used. Thus two distinct remaining
sources fill02,13.

If F is the supported pair, use target {01,03,12,23}. The same
four peripheral assignments fill01,10,23,32, and two remaining
sources fill03,12. Their class incidences are A,B on both, P,R
on03, and Q,S on12. The same count proves the allocation.

Thus four peripheral classes always give an opposite assembly.

## 3. Exactly three peripheral classes occur

Normalize p,q,r>0 and s=0. Since p+q+r≤9, we have a+b≥2.
Two actual sources from A,B can therefore fill either pair E or F
in its forward direction.

### 3.1 An opposite source contains edge 23

Among the varieties high on T, those containing23 are exactly

    W_E={01,02,13,23}, W_F={01,03,12,23}.

Suppose W_F occurs; the other case is symmetric in E,F. Reserve
that source at32. Each of the two other opposite varieties meets E,
because W_F is the unique high variety whose entire T-intersection
is F. If the other two can match the two edges of E, put them at
20,31 and use target W_E.

Otherwise both have exactly the same singleton intersection with
E. As their high patterns are distinct, they are the two adjacent
edge pairs joining that singleton to the two different edges of F.
They therefore match the two edges of F. Put them in the reverse
directions30,21, and use target W_F instead.

In either case the three opposite sources fill the reverse directions
of E or F and the corner32. The adjacent sources P:01, Q:10,
R:23, together with two A,B sources on the forward pair, complete
the target. All eight sources are distinct.

### 3.2 No opposite source contains edge 23

The high varieties avoiding23 are the following five:

| Variety | Underlying edges | Meets03? | Meets13? |
| --- | --- | --- | --- |
| 01|23 | 02,03,12,13 | yes | yes |
| 14|23 | 12,13,24,34 | no | yes |
| 04|23 | 02,03,24,34 | yes | no |
| 01|34 | 03,04,13,14 | yes | yes |
| 01|24 | 02,04,12,14 | no | no |

Among three distinct rows, at least one meets03, at least one
meets13, and at least two meet their union. Thus two distinct
opposite sources fill30,31 on target T'=01|34.

Put P at41 and Q at40. Four forward positions remain:

    03,04,13,14.

The A and R sources contain this whole rectangle. Moreover
a+r≥2, since the complementary three counts b,p,q total at most
nine. Put two A,R sources at04,14. Of the seven adjacent sources
still unused, at least five can fill03 and at least five can fill13:
only Q misses03 and only P misses13, and at most three sources
supporting either position have already been used. Equivalently,
the two neighbour counts are11−q−3 and11−p−3, each at least five.
Choose distinct sources for03,13.

This uses two opposite and six adjacent sources and assembles T'.

All support cases are covered, proving the lemma. The only finite
table is the five high varieties avoiding one specified diagonal;
it is immediate from the six possible two-edge intersections with T.
