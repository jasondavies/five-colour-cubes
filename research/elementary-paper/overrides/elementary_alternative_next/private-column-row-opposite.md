# A private adjacent column and a row opposite source

4 November 2026

**Status: elementary proof; independent root audit passed.**

## Theorem

Take three sources of class A=C(01) and eleven other adjacent sources,
each class having multiplicity at most three. Suppose every outsider
avoids02 and12. Adjoin the opposite source

    O={13,14,23,24}=12|34.

The resulting fifteen sources contain an opposite-target assembly.
Exchanging0,1 gives the other labelled row-intersection type.

Together with the high and diagonal notes, this proves the following
uniform statement: three sources of an adjacent class, eleven capped
adjacent outsiders avoiding one of its columns, and any opposite
source avoiding that column always assemble a five-colour target.

## 1. Notation and the two high-target tests

Use the eleven outsider classes of `private-column-high-opposite.md`:

    P=C02, Q=C12, L3=C123, L4=C124,
    R3=C023, R4=C024, H=C012,
    B=C234, Z23=C23, Z24=C24, Z34=C34.

Put x=z23,y=z24,w=z34 and

    L=b+l3+l4+q+x+y,       R=b+p+r3+r4+x+y,
    a=b+l3+x+w,            c=b+l4+y+w.

These count the outsider neighbours of20,21,30,40 respectively.
All outsider counts are at most three, and sum to eleven.

The target01|23 assembles exactly when

    L≥1, R≥1, a≥1, L+w≥2.                           (I)

This is the Hall test proved in Section1 of
`private-column-diagonal-opposite.md`: on this target the present O
has exactly the same intersection {13,31} as the opposite source
in that note. The proof therefore transfers unchanged.

Exchanging3,4 preserves the present O, and gives the second test:
target01|24 assembles exactly when

    L≥1, R≥1, c≥1, L+w≥2.                           (II)

We will also use the following explicit completion on target

    T={12,14,23,34}.

If r3≥1,r4≥2 and p+r3+r4≥4, fill

    A:12,14; O:32; R3:34; R4:41,43;
    another source from P,R3,R4:21;
    one Q or H source:23.                            (C)

The unused source at21 exists by the total p+r3+r4≥4, since only
three of those sources have been used. Each of those three classes
has corner21. A Q or H supplies23 independently. If instead r4≥1,
r3≥2, interchange3,4 throughout(C); its last position becomes24,
also supplied by Q or H. All sources in either matching are distinct.

## 2. No outsider sees21

Suppose R=0. Only Q,L3,L4,H,Z34 remain, so

    q+l3+l4+h+w=11.                                (2)

If w>0, use target01|34, put O at31, and fill the other reverse
positions30,40,41. For w≥3 use three Z34 sources. For w=2, the
inequality l3+l4+w≥5 gives an L3 or L4 source at30 or40; the two
Z34 sources fill the other positions. For w=1, it gives l3+l4≥4,
so both classes occur; use L3:30,L4:40,Z34:41. There is an unused
forward helper from Q or H because q+h≥2. It and three A sources
fill the forward half.

It remains that w=0. Then q,l3,l4,h sum to eleven, so each is at
least two. The target {02,04,23,34} has the explicit assembly

    A:02,04; Q:20,23; L3:34; L4:40,43; O:32.

Thus R=0 always solves.

## 3. No outsider sees20

Suppose L=0. Only P,R3,R4,H,Z34 remain, and

    p+r3+r4+h+w=11.                                (3)

If w≥2, again use target01|34. With w≥3, put O at31 and use
three Z34 sources at30,40,41. If w=2, there is an R3 or R4 source
because r3+r4+w≥5. Use that source at31 or41, O at the other of
those two positions, and two Z34 sources at30,40. In either case
p+h≥2 supplies a forward helper from P or H, which completes the
forward half together with three A sources.

If w≤1, equation(3) implies

    p+r3+r4+h≥10.

All four counts are positive; otherwise the other three have total
capacity nine. Moreover r3+r4≥4 and p+r3+r4≥7. Thus one of r3,r4
is at least two, and completion(C), or its image under3↔4, works
using an H source at23 or24. This closes L=0.

## 4. Both20 and21 are supported

Now L,R≥1. If w>0, both high-target tests hold. Assume w=0.

### L=1

The equation

    b+l3+l4+q+x+y=1

says that exactly one outsider occurs among those six classes.
The other ten outsiders are in P,R3,R4,H. Thus

    p+r3+r4+h=10.

Each of these four counts is positive, r3+r4≥4, and
p+r3+r4≥7. Completion(C), or its3↔4 image, works with an H
source. The exceptional outsider is not needed.

### L≥2

If both high targets fail, (I) and(II) force a=c=0. Hence

    b=l3=l4=x=y=w=0.

The only outsiders are P,Q,R3,R4,H, with

    p+q+r3+r4+h=11,     q=L≥2.                     (4)

If p≥2, at least one of R3,R4 occurs: otherwise p+q+h≤9.
An R4 source gives target {01,02,14,24} by

    Q:10,20; A:02,14; P:01,24; R4:41; O:42.

An R3 source gives the3↔4 image of this matching. Thus p≥2 solves.

If p≤1, equation(4) gives

    r3+r4≥4,     p+r3+r4≥5.

Both R3,R4 are positive, since each count is at most three, and
at least one is at least two. Use completion(C), or its3↔4 image,
with one of the Q sources at23 or24. This solves the last case.

All possible values of L,R,w have been covered, proving the theorem.

## Uniform private-column consequence

An opposite source avoiding02 and12 has exactly five possible
varieties. It either omits colour2, giving the three pairings of
0,1,3,4, or omits0 or1, giving one pairing in each case. Their
three stabilizer types are:

| Type | Representative | Proof |
| --- | --- | --- |
| High rectangle | {03,04,13,14} | `private-column-high-opposite.md` |
| Diagonal pair | {01,04,13,34} | `private-column-diagonal-opposite.md` |
| Row pair | {13,14,23,24} | This note |

If all of0,1,2 occurred in an opposite four-cycle avoiding both
edges02,12, its two-element bipartition part containing2 would
also need to contain0,1, impossible. This proves the five-variety
list directly.

