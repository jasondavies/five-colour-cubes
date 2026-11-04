# Eliminating four-position Hall covers for 2D+P

4 November 2026

**Status: elementary proof; independent root audit passed.**

Let the pool contain 2D+P, where D and P are distinct opposite
varieties, and eleven adjacent sources of class multiplicity at most
three. Suppose, for contradiction, that the pool has no assembly.

This note proves that all twelve sources other than D,D have their
D-intersections inside a five-position set H. In particular there
is no four-position cover with one exceptional source. The proof
does not enumerate source inventories.

We use two earlier facts:

* A triple adjacent class has at most one adjacent source disjoint
  from it. Otherwise three copies of the class, two disjoint
  adjacent sources and the three diffuse opposite sources assemble;
  see Section 3 of `../mixed_diffuse/five-class-mixed-hand-proof.md`.
* Nine adjacent cubes cannot all avoid two underlying edges in a
  failure with an opposite source and class cap three. The short
  cut proof is in `../four_opposite_root/common-high-targets.md`,
  Section 1, and does not require four opposite sources.

## 1. The initial Hall cover

Use D as target. Its two copies are universal. Hence the other twelve
sources have matching rank at most five on its eight positions.
König's theorem gives a set H of corner vertices and some exceptional
source vertices, with total size at most five, covering all incidences.

Each adjacent class meets D in two or four positions. At most two
classes fit in a two-position set, and at most three fit in a
three-position set. These facts are proved in Section 1 of
`../four_opposite_lowrep/four-distinct-opposites.md`.

Thus |H|≤2 is impossible: at least five of the eleven adjacent
sources would remain exceptional when |H|=2, exceeding the allowance
of three. Smaller H is still less possible. If |H|=3 and P is
exceptional, at most one adjacent source may be exceptional, whereas
ten do not fit in three positions. If P is contained in H, then H
contains a bidirected edge; a three-position set of that form supports
at most two adjacent classes, hence six copies, again insufficient.

Therefore either |H|=5 and every source is contained in H, or |H|=4
and at most one source is exceptional. We exclude the latter case.
At least ten adjacent sources then have their D-intersections in H.
If P is exceptional, all eleven adjacent sources are contained.

Normalize D={13,14,23,24}. An edge denotes both directions unless
individual corners are listed.

## 2. The ten four-position shapes

Up to symmetries of the target and reversal of all directions,
four positions in a bidirected four-cycle have ten shapes. To see
completeness, count complete bidirected edges in H. There are two
forms with two such edges, four forms with one, and four orientations
of the entire four-cycle with none. The adjacent classes whose
D-intersection lies in H are as follows; C(S) means S→Sᶜ.

| H | Eligible outsets S |
| --- | --- |
| 13,14,23,24 | 01;02;124;123;12;012 |
| 13,14,23,31 | 01;124 |
| 13,14,23,32 | 01;124;13;013 |
| 13,14,23,42 | 01;124;14;014 |
| 13,14,31,32 | 01;03;13;013 |
| 13,14,31,41 | 01;234 |
| 13,14,31,42 | 01;14;014 |
| 13,14,32,42 | 01;134;13;14;014;013 |
| 13,24,31,42 | 14;023;23;014 |
| 13,24,32,41 | none |

Each row follows directly by imposing the missing directed-cut
conditions on a two- or three-element outset. Rows with at most
three classes cannot accommodate ten contained adjacent sources.
The ninth row makes at least ten sources avoid the other two
underlying target edges, contradicting the nine-avoider fact.

The fourth and eighth rows contain no complete bidirected edge,
so P is exceptional and all eleven adjacent sources are contained.
Their classes share respectively corner 13 and corner 12. The
common-corner eleven-source theorem in
`common-corner-eleven-hand.md` solves them.

The first, third and fifth rows remain.

## 3. A directed rectangle containing all eleven adjacent sources

In the first row P is exceptional. Write

    A=C(01), B=C(02), C=C(124), E=C(123),
    U=C(12), V=C(012),

with counts a,b,c,e,u,v, each at most three and summing to eleven.
We prove that these sources and D,D assemble; P is unnecessary.

### 3.1 All four star classes occur

If a,b,c,e are positive, use target O61={12,14,23,34}. Put D,D at
41,32, and use

    A:12; B:21; C:43; E:34.

Two unused adjacent sources fill 14,23. Among the unused sources,
at least a+e+u+v−2≥3 see 14, and at least b+c+u+v−2≥3 see 23.
Two distinct sources can therefore be chosen.

### 3.2 Some star class is absent

The symmetries interchanging 1,2, interchanging 3,4, and reversing
directions while interchanging the two parts of D act transitively
on A,B,C,E. Assume a=0.

If c,e>0, use target O63={03,04,23,24}. Put D,D at32,42, C at40,
and E at30. The B/V sources are universal on 03,04,23,24. Their
number satisfies b+v≥2, since c+e+u≤9 and the total is eleven.
Use two of them at03,04. The remaining adjacent neighbours of23
number at least b+v+c+u−3=8−e≥5; those of24 number at least
b+v+e+u−3=8−c≥5. Thus two further distinct sources fill23,24.

Otherwise one of C,E is absent as well. There cannot be three
absent stars, since the three remaining classes would have total
capacity nine. We are left with one A/B star, one C/E star, and
U,V. All four counts are at least two and exactly three are three.
Normalize the support to A=C(01), C=C(124), U=C(12), V=C(012).

### 3.3 The four-class residual

Both U and V have own loops already when all four counts are two:

    reserve two U: A:13,14; C:10,20; V:23,24;
    reserve two V: A:03,04; C:13,23; U:14,24.

The own-loop restoration argument gives the conflict edges A–U and
C–V, whose pole pairs intersect. Three further edges have the
following completions, after the indicated pair is reserved:

| Reserved pair | Target class | Tricoloured completion |
| --- | --- | --- |
| A,V | C | C:40,43; A:13; U:10,20; V:23 |
| C,U | A | A:02,12; V:03,04; C:13; U:14 |
| U,V | C(14) | C:40,43; A:12,13; D:42; U:10 |

If U,V are both triples, their conflicting three-element repeat
sets would require six colours. If U is doubled, V is a triple and
the conflict triangle U,V,A requires at least 2+3+1=6 colours.
If V is doubled, use the triangle U,V,C instead. These exhaust
the possible positions of the unique double. Thus the first row
is completely excluded.

## 4. The row H={13,14,23,32}

The contained classes are

    A=C(01), B=C(124), C=C(13), E=C(013).

The classes B,E are disjoint. If all eleven adjacent sources were
contained, their counts would be 3,3,3,2. At least one of B,E would
then be a triple with at least two disjoint sources, impossible.

Consequently P is contained and ten adjacent sources are contained.
Retain ten if necessary. All four contained classes occur, since
any three have capacity nine. The only possible P are

    O64={02,04,23,34}, O73={01,03,12,23}.

For P=O64, use target O63 and assign

    D:24,42; P:23; A:03; B:40; C:30.

The remaining positions04,32 are filled by two remaining sources
from A,C,E. At least a+c+e−2=8−b≥5 such sources remain. Each meets
04 or32, and E supplies both, so a two-position matching exists.

For P=O73, use target O61 and assign

    D:23,41; P:21; B:43;
    four C/E sources:12,14,32,34.

The C/E sources are universal on those four positions and c+e≥4,
because a+b≤6. Both possibilities therefore assemble.

## 5. The row H={13,14,31,32}

The contained classes are

    A=C(01), B=C(03), C=C(13), E=C(013).

### 5.1 P is contained

The only choices are P=O67={01,04,13,34} or
P=O72={02,03,12,13}. At least ten adjacent sources are contained;
retain ten. All four classes are positive.

For P=O67, target O66={03,04,13,14} has the assignment

    P:40; D:13,41; A:03; B:31; C:30.

The two remaining positions04,14 are filled by unused adjacent
sources. Seven remain, each meeting04 or14, and E supplies both.
Thus two distinct sources suffice.

For P=O72 and c≥2, use target O73={01,03,12,23}:

    P:21; D:23,32; A:03; B:01; C:10,30; E:12.

If c=1, the other three counts are all three. Use target
O74={01,02,13,23} instead:

    P:20; D:23,31; C:10; B:01; A:02,13; E:32.

### 5.2 P is exceptional

Now all eleven adjacent sources are contained, with counts3,3,3,2.
Whenever A is a triple it has an own loop, using

    A:03; D:13; B:02,04; C:12,14

after two A reservations. Likewise a B triple has an own loop via

    B:01; D:31; A:02,04; C:32,34.

The class E has an own loop already at counts two in the other
classes, using A:02,04; B:32,34; C:12,14.

If A and B are both triples, their own loops conflict at the common
pole0 and give an assembly. Otherwise the unique double is one of
A,B; the other and E are both looped triples. Their conflict edges
are witnessed as follows:

| Reserved pair | Target | Tricoloured completion |
| --- | --- | --- |
| A,E | C(034) | B:01,31; A:02; D:41,42; C:32 |
| B,E | C(012) | A:03,13; B:04; D:23,24; C:14 |

Again two conflicting triple classes would require six repeated
colours, impossible.

Every four-position cover is now excluded. By Section 1, failure
forces a five-position set H containing the D-intersections of P
and of all eleven adjacent sources. Equivalently, three target
positions are absent from P and the entire adjacent pool.
