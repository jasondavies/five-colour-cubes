# A private adjacent column and a diagonal opposite source

4 November 2026

**Status: elementary proof; independent root audit passed.**

## Theorem

Take three sources of class A=C(01) and eleven other adjacent sources,
each class occurring at most three times. Suppose every outsider avoids
02 and12. Adjoin

    O={01,04,13,34}=03|14.

Every undirected edge denotes both directed corners. These fifteen
sources contain an eight-source five-colour assembly.

This is the diagonal-intersection type of an opposite source avoiding
a private column of A. Exchanging colours3,4 gives the other labelled
variety of the same type. No assumptions about other private columns,
own loops, or occupied-class counts are used.

## 1. Outsiders and two high-target tests

Use the eleven names from `private-column-high-opposite.md`:

    P=C02, Q=C12, L3=C123, L4=C124,
    R3=C023, R4=C024, H=C012,
    B=C234, Z23=C23, Z24=C24, Z34=C34.

Their reverse-A intersections are displayed in that note. Write
x=z23, y=z24, w=z34 and use lower-case letters for all other counts.
Every count is at most three and their sum is eleven. Put

    L=b+l3+l4+q+x+y,       R=b+p+r3+r4+x+y,
    a=b+l3+x+w,            d=b+r4+y+w.

These are respectively the outsider neighbour counts of20,21,30,41.

Target01|23 assembles exactly when

    L≥1, R≥1, a≥1, L+w≥2.                           (I)

Target01|24 assembles exactly when

    L≥1, R≥1, d≥1, R+w≥2.                           (II)

Here is a direct Hall verification of(I). The core A,A,A,O supplies
the four forward positions through A and the two positions13,31
through O. The potentially deficient reverse sets are the singleton
corners20,21,30 and the pair{20,30}; their outsider neighbour counts
are precisely the four expressions in(I).

Every other reverse set is automatic under(I). The pair{20,21}
has at least five outsider neighbours, since only H,Z34 avoid it.
The pair{21,30} has at least two, since its only avoiding classes are
Q,L4,H. Pairs containing31 also have O and an outsider from their
other corner. A reverse triple containing both20,21 inherits five
outsider neighbours. The triple{20,30,31} inherits L+w≥2 neighbours;
the triple{21,30,31} has at least two by the same Q,L4,H bound.
The full reverse half sees all outsiders except H, hence at least
eight.

A set meeting A and O has four core neighbours. If it meets A but
avoids O, a four-position set must contain at least one of20,21,30,
which is supported by(I). For larger sets, use the elementary cut
bounds: at most three classes fit inside three specified target
positions and at most two fit inside two. Thus a five-set has at
least two outsider neighbours, a six-set at least five, and a seven-
or eight-set all eleven. These counts cover every remaining Hall
inequality. Necessity of(I) follows from its listed singleton and
pair sets. The argument for(II) follows by the symmetry
(0 1)(3 4), which preserves O and exchanges L,R and a,d.

## 2. If 20 or21 is absent

The same symmetry lets us assume R=0. All outsiders then belong to

    Q,L3,L4,H,Z34,

and

    q+l3+l4+h+w=11.                                (2)

Suppose w>0. Use target01|34 and put O at31. Its other three reverse
positions are30,40,41. If w≥3, three Z34 sources fill them. If w=2,
equation(2) and q,h≤3 give l3+l4≥3; choose one L3 or L4 at its
corner30 or40 and let the two Z34 sources fill the other positions.
If w=1, then l3+l4≥4, so both are positive; use L3:30,L4:40,Z34:41.

There is a remaining forward helper from Q or H: their combined
count is at least two because l3+l4+w≤9. It and three A sources
fill the forward half. Thus w>0 always gives an assembly.

Failure therefore forces w=0. The four counts q,l3,l4,h sum to eleven,
so they are 3,3,3,2 in some order. Section4 closes this family.

## 3. If both 20 and21 are present

Assume L,R≥1. If w>0, both(I) and(II) hold, so suppose w=0.
To fail both targets we need

    (a=0 or L=1) and (d=0 or R=1).                  (3)

The alternatives involving L=1 or R=1 are incompatible with eleven
outsiders. If L=R=1, the total is

    h+L+R-(b+x+y)≤5.

If L=1 and d=0, then b=r4=y=0 and the total is

    h+L+p+r3≤3+1+3+3=10.

The remaining mixed alternative is symmetric. Thus(3) forces a=d=0.
Consequently b=l3=x=r4=y=w=0, and only

    P,Q,L4,R3,H

remain, with

    p+q+l4+r3+h=11.                                (4)

Use O itself as a target, with positions

    01,10,04,40,13,31,34,43.

The two L4-only outer positions are40,43; the two R3-only outer
positions are31,34. If l4,r3≥1 and l4+r3≥3, these four positions
can be filled by L4,R3,O, using O to assist whichever class has
only one source, if necessary.

When p,q>0, finish with P:01,Q:10 and A:04,13. If p=0, equation(4)
forces q,l4,r3,h each to be at least two. Use

    L4:40,43; R3:01,34; O:31; Q:10; A:04,13.

If q=0, the symmetric explicit matching is

    R3:31,34; L4:10,43; O:40; P:01; A:04,13.

The possibility p=q=0 is excluded by total capacity. Hence this
target solves whenever l4,r3≥1 and l4+r3≥3.

Only three count forms remain:

1. l4=0 and p,q,r3,h are 3,3,3,2;
2. r3=0 and p,q,l4,h are 3,3,3,2;
3. l4=r3=1 and p=q=h=3.

These are direct consequences of(4), not an inventory list used as
a premise. All are closed in Section4.

## 4. Explicit loops finish all count forms

Two own-loop triples whose pole pairs intersect always assemble:
otherwise each triple must use all three allowed repeated colours;
choose a common repeat and use one cube from each at the bicoloured
corners of the first target. Restoring one universal cube in the
first class's loop matching replaces the reserved cube of the second
class if it was used. This argument is detailed in the high-type
note and remains valid when O is used in a loop.

### The family q,l3,l4,h=3,3,3,2

A triple H has the loop

    A:03,04; L3:14,24; L4:13,23.

A triple L3 has the loop

    remaining L3:30; O:34; A:14; L4:20; Q:10,24.

A triple L4 has the loop

    remaining L4:43; O:40; A:13; L3:20; Q:10,23.

If h=3, one of L3,L4 is a triple and its poles meet H's poles34.
If h=2, both L3,L4 are triples and their poles04,03 meet. Thus the
family solves in every case.

### The families involving P,Q,L4,R3,H

Whenever p=3 and q≥2, P has the loop

    remaining P:21; O:01; A:03,04; Q:23,24.

Whenever q=3 and p≥2, Q has the loop

    remaining Q:20; O:10; A:13,14; P:23,24.

If p=q=3, these two triples have intersecting poles02,12 and solve
immediately. This includes the third count form above.

In the first count form, if p and q are not both three, then
r3=h=3 and p,q≥2. The H loop is

    A:03,04; P:23,24; Q:13,14,

and the R3 loop is

    remaining R3:34; O:31; A:04; P:01,21; Q:24.

Their pole pairs34 and14 intersect. In the second count form the
same reasoning gives l4=h=3 and p,q≥2. Use the same H loop and

    remaining L4:43; O:40; A:13; Q:10,20; P:23.

The pole pairs34 and03 intersect. Every matching uses distinct
physical sources and respects the minimum counts in its case.

This completes the theorem.

## Scope

Together with `private-column-high-opposite.md`, this settles two of
the three geometric types of opposite sources avoiding a column of
an adjacent triple. The row-intersection type is proved in
`private-column-row-opposite.md`. The sole-triple predecessor is
excluded by `five-repeated-classes-two-helpers.md`; the complete
one-opposite route is joined in `one-opposite-fourteen-adjacent.md`.
