# Five-position covers with a missing bidirected edge

4 November 2026

**Status: elementary proof; independent root audit passed.**

Keep the setting of `hall-four-cover-hand.md`: the pool consists of
2D+P, D≠P, and eleven adjacent sources with class cap three. In a
hypothetical failure, every adjacent triple has at most one adjacent
source disjoint from it. The preceding note reduces failure to a
five-position set H containing the D-intersections of P and all
eleven adjacent sources.

This note closes the cases where the three omitted D positions
include both directions of an edge. It follows in particular that
the whole neighbouring pair case is solved.

Normalize D={13,14,23,24}. The omitted set consists of a bidirected
edge and a further directed corner. There are exactly two geometries,
according as their underlying edges meet or are disjoint.

## 1. The two edges meet

Normalize the omitted corners to24,42,41. The containing set is

    H={13,14,23,31,32}.

The adjacent cuts avoiding those three corners are exactly

    A=C(01), B=C(03), C=C(124), E=C(13), F=C(013).

Write their counts as a,b,c,e,f. They sum to eleven and are at most
three. The class C is disjoint from B and F.

If c=3, the disjoint-source bound gives b+f≤1, whence the total
is at most3+3+3+1=10. Thus c≤2. If c=0, all eleven adjacent
sources have their D-intersections in {13,14,31,32}; Section 5.2
of `hall-four-cover-hand.md` gives an assembly using D,D alone.

Suppose c>0. All five classes occur. For c=1, the other four
counts sum to ten, forcing all four positive. For c=2, neither B
nor F may be a triple, since either would have two disjoint C
sources. Hence b,f≤2. Omitting B or F would give total at most
3+3+2+2=10; omitting A or E gives an even smaller bound. Again all
four other classes are positive.

Use target O66={03,04,13,14}, with

    D:13,41; A:03; B:31; C:40; E:30.

Two more adjacent sources fill04,14. At least

    a+b+e+f−3 = 8−c ≥ 6

unused sources from A,B,E,F remain, and each meets04 or14. A
remaining F sees both, so two distinct sources can fill the pair.
This proves the case. P is unnecessary in the displayed assembly.

## 2. The two edges are disjoint

Normalize the omitted corners to24,42,31, so

    H={13,14,23,32,41}.

The eligible cuts are

    A=C(01), B=C(124), C=C(13),
    E=C(024), F=C(24), G=C(013).

Let their counts be a,b,c,e,f,g, with sum eleven and cap three.
Put

    x=c+g, y=e+f, L=a+x, R=b+y.

The class F is disjoint from every class in the left group
{A,C,G}, while G is disjoint from every class in the right group
{B,E,F}. We first show

    x>0, y>0, L≥3, R≥3.

If x=0, only A,B,E,F remain. Their eleven cubes have counts3,3,3,2.
The disjoint classes A,F each have at least two cubes and at least
one is a triple, contradicting the disjoint-source bound. Similarly,
y=0 leaves A,B,C,G and the disjoint pair B,G, giving a contradiction.

If L≤2, then R≥9. The three right classes have cap three, so
R=9, L=2 and b=e=f=3. The F triple has two disjoint left sources,
again impossible. Interchanging the roles gives R≥3 as well: if
R≤2, then a=c=g=3 and the G triple has two disjoint right sources.

Now use target O61={12,14,23,34}. Its adjacent intersections split
into two four-position halves:

| Source group | Available positions |
| --- | --- |
| A | 12,14 |
| C,G | 12,14,32,34 |
| B | 23,43 |
| E,F | 21,23,41,43 |

Put the two D copies at32,41. Since x>0 and L≥3, choose one C/G
source at34 and two further A/C/G sources at12,14. Since y>0
and R≥3, choose one E/F source at21 and two further B/E/F sources
at23,43. These eight assignments are compatible and use distinct
physical cubes. Again P is unnecessary.

Both missing-bidirected-edge geometries therefore assemble.

## 3. Consequence: the neighbouring profile 2,1 is closed

If D and P share two underlying edges, their D-intersection consists
of two complete bidirected edges. A five-position containing set H
must contain those four positions. Its three-position complement
therefore consists of one complete bidirected edge and one further
directed corner. Sections 1 and 2 exclude it.

Combining with `hall-four-cover-hand.md` proves:

> Two copies of one opposite variety D and one copy of a distinct
> neighbouring variety P, together with eleven adjacent cubes of
> class cap three, always assemble a five-colour target.

For a nonneighbouring P, the only cases still left after these
reductions have three omitted corners on three distinct underlying
edges. These edges form the three-edge path complementary to D∩P
inside D. Under symmetries of D, the three omitted directions have
three patterns: monotone, one change, and alternating. In using this
normalization one must retain both possible choices of P sharing
the remaining edge: path reversal need not preserve the marked
single variety P. Equivalently, after fixing the ordered pair D,P,
direction reversal leaves four oriented path cases, with the two
one-change forms distinguished.
