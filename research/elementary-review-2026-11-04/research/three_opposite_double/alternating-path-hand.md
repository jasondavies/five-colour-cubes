# The alternating missing path for 2D+P

4 November 2026

**Status: complete hand argument; independent root and alternative-agent
mathematical audits passed.**

Let

    D=O60={13,14,23,24}, P=O67={01,04,13,34}.

Take two D sources, one P, and eleven adjacent sources of class cap
three, all avoiding the corners32,41,42. The latter directions
alternate along the three-edge path3–2–4–1 in D. We prove assembly.

The eight allowed adjacent classes and their counts are

| Count | Class |
| --- | --- |
| a | A=C(01) |
| b | B=C(02) |
| c | C=C(124) |
| d | E=C(123) |
| e | F=C(12) |
| f | G=C(023) |
| g | H=C(23) |
| h | J=C(012) |

All counts lie between zero and three and sum to eleven. The class
names are used for physical sources; lower-case letters denote their
counts. A triple class has at most one source disjoint from it in a
failure, by the earlier three-opposite/disjoint-source construction.
We also use `common-corner-eleven-hand.md`.

Split according to c, the number of C(124) sources.

## 1. The case c=0

On target O63={03,04,23,24}, put D,D at32,42 and P at40. The five
remaining positions are03,04,23,24,30. The adjacent intersections
are described by the groups

    A:03,04;
    B,J:03,04,23,24;
    E,H:24,30;
    F:23,24;
    G:04,24.

These five positions can be matched whenever

    d+g>0, a+b+h>0, b+h+e>0.                 (1)

Here is the Hall verification. Choose one E/H at30. Put X=b+h
and Y=d+g. On the remaining four positions,03 and23 have
neighbour counts a+X and X+e. The pair03,04 has at least
a+X+f≥2 neighbours because its complementary source groups Y,e
have capacity at most6+3=9. Similarly the pair03,23 has at least
a+X+e≥2 neighbours because Y,f have capacity at most nine. All
other two-position inequalities follow either from these or from
at least ten minus one class neighbours. The only triple not seeing
all ten remaining sources is03,04,23; it sees11−Y≥5. Thus (1)
suffices.

If (1) holds, we have an opposite assembly. Otherwise consider the
three possible zero sums.

### 1.1 a=b=h=0

Only E,F,G,H remain, with eleven sources. All four classes contain
corner24. The common-corner eleven theorem gives an assembly.

### 1.2 b=h=e=0

Only A,E,G,H remain. Their eleven counts have profile3,3,3,2, so
each is at least two. Target O71={01,02,14,24} has the assignment

    D:41,42; P:01; A:02,14; E:10,20; G:24.

### 1.3 d=g=0

Only A,B,F,G,J remain. If a=0, all present classes contain24. If
e=0, all present classes contain04. Either case is covered by the
common-corner theorem.

Assume a,e>0. The counts give

    b+f≥2, a+e+h≥5.

Use target O71 with

    D:41,42; P:10; A:02; F:20;
    two B/G sources:01,24;
    one further A/F/J source:14.

The last source exists after the A,F reservations because at least
five sources lie in those three classes. This completes c=0.

## 2. The case c=1

On O63, D,D again fill32,42. The single C source sees23,40 and
P sees04,40. Thus one of these two sources can fill40 and the other
can be used at either04 or23, according to which source fills40.
For matching purposes the ten remaining adjacent sources therefore
have one extra flexible source on {04,23}.

This gives an assembly whenever

    d+g>0, a+b+h>0.                          (2)

Indeed put one E/H at30. On03,04,23,24, the extra source supplies
04 or23. Corner03 has a+b+h>0 neighbours. Corner24 has at least
nine minus a≥6 adjacent neighbours. The pairs03,04 and03,23
have at least two neighbours, using the extra source. The only
potentially small triple03,04,23 has at least10−(d+g)≥4
neighbours. All other Hall inequalities are automatic from these
counts. If the extra source is assigned04, use P there and C at40;
if it is assigned23, use C there and P at40. If it is unused, put
either eligible source at40 and discard the other.

### 2.1 d=g=0

The other ten adjacent sources are A,B,F,G,J. If a>0, then
b+f>0 because the other three classes have capacity nine. On O71,
assign

    D:41,42; P:10; C:20; A:02;
    one B/G source:01.

The remaining positions14,24 have respectively at least
a+e+h−1≥3 and b+f+e+h−1≥6 unused neighbours, so distinct
helpers fill them.

If a=0, the four counts b,e,f,h sum to ten, so all are positive.
Use P itself as target, with

    D:13,31; P:43; C:40; G:34; F:10; B:01; J:04.

### 2.2 a=b=h=0

The four counts d,e,f,g sum to ten and are all positive. If f≥2,
again use target P:

    D:13,31; P:43; C:40; G:01,04; F:10; H:34.

If f=1, then d=e=g=3. The pool contains the smaller core

    one D +3C(12)+3C(23)+2C(123).

This core assembles by the nine-source union-class lemma: C(12)
and C(23) have the common pole2, their union class is C(123), and
D contains the edge13 joining their other two poles. The lemma's
proof is Section 2 of
`../three_opposite_root/repeated-colour-closures.md`. The singleton
C(124) and C(023) sources are unnecessary.

Thus c=1 is closed.

## 3. The cases c=2 or3

Use P as target. Put D,D at13,31 and two C sources at40,43. If
the other adjacent sources can match any three positions of

    K={01,04,10,34},

P fills the fourth and the target is complete. Their K patterns are

    A,J:{04}; B:{01,04}; E:{10,34};
    F:{10}; G:{01,04,34}; H:{34}.

There are11−c≥8 such sources. If their matching rank is at most
two, König's theorem confines all their patterns to two K positions.
A cover using one corner and one exceptional source would require
at least seven sources at one corner; at most six can be confined
to04, and at most three to any other corner. A cover with only
source vertices is also impossible.

The only two-position sets accommodating eight sources are:

| Positions | Eligible classes besides C |
| --- | --- |
| 01,04 | A,B,J |
| 04,10 | A,F,J |
| 04,34 | A,H,J |
| 10,34 | E,F,H |

The other two pairs admit at most one class. In each displayed row
all three classes occur at least twice, so with C the full adjacent
profile is3,3,3,2.

For the second row, all eleven adjacent sources contain13; for the
fourth, all contain20. The common-corner theorem solves both.

The third row is impossible in a failure: A and H are disjoint,
both have at least two copies, and at least one is a triple. If
both had only two, even three each of C,J would give total only ten.

For the first row, use target O61:

    D:32,41; P:34; A:12,14; B:21; C:43; J:23.

All assignments respect the lower bound of two per class. This
completes c≥2 and hence the alternating-path case.

## Symmetry and scope

The other possible single opposite variety in this normalized
alternating five-position cover is O72={02,03,12,13}. Reversing
the path by (1 3)(2 4) and reversing all directed corners preserves
the absent alternating directions and exchanges O67,O72. It also
preserves D. Thus the proof covers both singles, with source class
names permuted accordingly.

The cut list follows directly from the three forbidden directions.
All count reductions and matching criteria above are proved by Hall
and the class caps; no inventory catalogue is used.
