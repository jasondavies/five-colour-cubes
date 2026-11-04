# A diagonal pair of private corners is impossible

**Elementary conditional lemma.** In a failing pure fourteen-cube pool
with class counts at most three, suppose every three-copy class has at
least two private corners. Then every three-copy class has exactly two
private corners in one column of its two-by-three array.

The row case is excluded in `g3-private-row-hand.md`. Any three private
corners contain a row pair, so exactly two remain. This note excludes
the diagonal possibility. It uses only small opposite-rectangle matchings
and the private-corner hypothesis.

## 1. The two three-class groups

Normalize A=C(01), with private corners02 and13. Its eleven outsiders
avoid these two corners and have exactly the following classes:

    X0=C13,  X1=C134, X2=C123,
    Y0=C02,  Y1=C024, Y2=C023,
    B=C234,  Z2=C34, Z3=C24, Z4=C23.

Write x_i,y_i for the six nonzero-class counts, x=Σx_i, y=Σy_i, and
z for the total B/Z count. Every individual count is at most3 and

    x+y+z=11.

Since A has exactly two private corners, the outsiders supply all four
of its other corners. Thus x,y>0. The reverse-A intersections are

| Class | Reverse-A corners |
| --- | --- |
| X0 | 30 |
| X1 | 30,40 |
| X2 | 20,30 |
| Y0 | 21 |
| Y1 | 21,41 |
| Y2 | 21,31 |

Each B/Z source supplies both reverse corners in at least two rows.

Two useful count bounds follow from private corners. If X1 or X2
occurs, X0 cannot occur three times: A and that class cover all but
one of X0's corners. Hence x0≤2 in that situation. Similarly y0≤2
if Y1 or Y2 occurs. In particular x,y≤8; when x2=0, x≤5, and when
y2=0, y≤5.

## 2. Matching a reverse rectangle suffices

If four outsiders match the reverse corners q0,q1,s0,s1 of any two
rows q,s, the corresponding opposite target is assemblable.

Here is a direct Hall justification that avoids reserving an extra
forward source. A set of at most three target corners meeting A has
the three A copies as neighbours. A set of four meeting A has an
additional outsider neighbour: if it contains a reverse corner this
follows from the assumed reverse matching; if it consists entirely of
forward corners, A has only two private corners. Sets disjoint from A
are covered by the reverse matching. Finally sets of at least five
corners satisfy Hall automatically. The complement of a five-set can
contain complete intersections of at most three adjacent classes,
hence at most nine of the fourteen sources; the complement of a six-set
contains at most two classes, hence at most six sources. Complements
of size at most one contain no source intersection.

There can be at most three zero sources. If z≥5, each reverse row
sees at least z−3≥2 of them, so four zeros match any reverse rectangle.
If z=4, some two rows each have degree at least two and their union
sees all four zeros, which again gives a reverse rectangle. Therefore

    z≤3.

The permutation (0 1)(2 3) interchanges X and Y, interchanges Z2,Z3,
and preserves the hypotheses. We use this symmetry below.

## 3. No zero sources

Now x+y=11, so x,y≥3. If x2,y2>0, match rectangle2,3 by

    X2:20; another X:30; Y2:31; another Y:21.

Thus by symmetry x2=0. Then x≤5 and y≥6. Both y1,y2 are positive,
since otherwise y≤5. If x1>0, rectangle3,4 is filled by

    X1:40; another X:30; Y2:31; Y1:41.

Hence x1=0. The count bounds force

    x0=3, y0=2, y1=y2=3.

But Y2 has at most one private corner: Y0 supplies01,04,21,24, and
X0 supplies34, leaving only31. This contradicts its count3.

## 4. Two or three zero sources

If the zero sources can match20 and31, use an X at30 and a Y at21
to complete rectangle2,3. Each zero contains at least one of the rows
2,3. With at least two zero sources, this two-position matching can
fail only when all zeros miss row2 or all miss row3. By symmetry they
are all Z2=C34.

If x2>0, two zeros fill40,41, an X2 fills20 and a Y fills21, giving
rectangle2,4. If y2>0, two zeros fill40,41, an X fills30 and a Y2
fills31, giving rectangle3,4. Hence x2=y2=0.

Now x+y=11−z is8 or9, while x,y≤5. If x1,y1>0, use

    X1:40; another X:30; Y1:41; a zero:31.

There is another X because x≥3. Thus x1=0 or y1=0.

If x1=0, the bounds force z=3, x0=3, y0=2, y1=3. The triple Y1
has at most one private corner: Y0 supplies01,03,21,23 and Z2
supplies41, leaving only43.

If y1=0, the symmetric count calculation gives z=3, y0=3, x0=2,
x1=3. Now X0 supplies10,12,30,32 and Z2 supplies40,42, so the
triple X1 has no private corners at all. Both alternatives contradict
the hypothesis.

## 5. One zero source

Here x+y=10, so x,y≥2.

If the zero is B or Z4, it contains both rows2,3. If x2>0, rectangle2,3
is supplied by X2:20, another X:30, Y:21 and zero:31. If y2>0, use
the symmetric assignment. Thus x2=y2=0, and the bounds force

    x0=y0=2, x1=y1=3.

Rectangle3,4 is then filled by X1:40, another X:30, Y1:41, zero:31.

Otherwise symmetry makes the zero Z2=C34. If x2>0, the same
rectangle2,3 construction works, so x2=0. Hence x≤5 and y≥5.
If y1,y2>0, rectangle3,4 uses X:30, zero:40, Y2:31 and Y1:41.
Therefore one of y1,y2 is zero. The bounds now force

    x0=2, x1=3, y0=2,

with exactly one of y1,y2 equal to3. If y1=3, use X1:40, another
X:30, Y1:41 and zero:31. If y2=3, Y0 supplies01,04,21,24, the
zero supplies31 and X0 supplies34; the triple Y2 has no private
corner, again impossible.

Every diagonal case has yielded an opposite assembly or violated the
private-corner hypothesis. Together with the row lemma, this proves
that all three-copy classes in the all-private branch have exactly
two private corners in a column.
