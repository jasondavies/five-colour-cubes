# Every non-own-loop triple has a private column

**Lemma.** In a failing pool of fourteen adjacent-repeat cubes, with
all tricoloured class counts at most three, every triple without an
own-orientation loop has exactly two private corners, in one column
of its two-by-three cut array.

The unconditional row lemma already gives exactly two private corners.
Here we exclude a diagonal pair even when the pool has one own-loop
triple. The proof uses `private-row-unconditional-hand.md`, the
nonprivate-triple lemma, and the two-own-loop-triple exclusion.

**Orientation convention.** For a positive class `C(pq)`, a row pair
has the same tail `p` or `q`. For a negative class `C(V\{p,q})`, a
row pair has the same head `p` or `q`. In particular the pairs
`40,42` in `C(134)` and `20,24` in `C(123)` are column pairs; we
make no row-based exclusion of them. 

## 1. The diagonal normal form and reverse rectangles

Normalize the distinguished triple to `A=C(01)` with private
corners `02,13`. Its eleven outsiders avoid these corners, and
have exactly the following possible classes:

\[
\begin{array}{lll}
X_0=C(13),&X_1=C(134),&X_2=C(123),\\
Y_0=C(02),&Y_1=C(024),&Y_2=C(023),
\end{array}
\]

together with `B=C(234)`, `Z_2=C(34)`, `Z_3=C(24)`, and
`Z_4=C(23)`. Let `x_i,y_i` be their counts, `x=Σx_i`, `y=Σy_i`,
and let `z` count the B/Z sources. Thus `x+y+z=11`.

A has exactly two private corners, so its other four corners are
covered by outsiders; in particular `x,y>0`. The reverse-A
intersections are as follows.

| Class | Reverse-A corners |
|---|---|
| `X_0` | `30` |
| `X_1` | `30,40` |
| `X_2` | `20,30` |
| `Y_0` | `21` |
| `Y_1` | `21,41` |
| `Y_2` | `21,31` |

Each B/Z source sees both reverse corners in at least two rows.

A matching of four outsiders to any reverse rectangle
`q0,q1,s0,s1` implies an opposite assembly. To verify Hall, a set of at
most three target corners meeting A has its three copies as neighbours.
A four-set meeting A gains an outsider from the reverse matching if it
meets the reverse half; otherwise A has only two private corners, so
the forward four-set also gains an outsider. Reverse-only sets are
covered by the assumed matching. For five- and six-sets, their complements
contain complete intersections of at most three and two adjacent classes,
respectively. The class cap gives at least $14-9=5$ and $14-6=8$
neighbours. A complement of at most one corner contains no whole source
intersection. These are all Hall inequalities.

It follows that `z<=3`. At `z>=5` each reverse row has at least
`z-3>=2` zero neighbours; at `z=4` some two rows each have degree
at least two. In either case four zeros match a reverse rectangle.

The permutation `(0 1)(2 3)` exchanges X and Y and exchanges
`Z_2,Z_3`. We will use this symmetry.

## 2. Preliminary restrictions if the base class is a triple

Suppose `x_0=3` and at least one of `x_1,x_2` is positive. A and
that branch cover all but at most one corner of `X_0`, so the
nonprivate-triple lemma gives `X_0` an own loop.

Its three cubes must use all three repeated colours outside its
pole pair `13`. Its reverse class `Y_1=C(024)` is therefore absent:
own-loop restoration makes classes with the same poles conflict,
and `Y_1` has the same three available repeated colours. Thus

\[
y_1=0.
\]

If `Y_0,Y_2` both occur, neither can be a triple. A and `Y_2`
cover all but corner `23` of `Y_0`, while `Y_0` and `X_0`
cover all but corner `31` of `Y_2`. A triple in either class
would have another own loop. Since at most one own-loop triple
is possible, both counts are at most two. If only one class is
present, its count is at most three. Consequently

\[
y\le4.
\]

Also `x_2<=2`. Indeed `X_0` covers four corners of `X_2`,
leaving only `20,24`. At least one of `Y_0,Y_2` occurs because
`y>0` and `y_1=0`; either covers `24`. Thus a triple `X_2`
would have at most one private corner and give a second own loop.
We have proved

\[
x_0=3,\quad x_2\le2,\quad x\le8,\quad
 y_1=0,\quad y\le4.
\]

## 3. The base-triple exception is impossible

Continue under the assumptions of Section 2.

### No zero sources

Now `x+y=11`, so `x>=7` and `y>=3`. In particular `x_2>0`.
If `y_2>0`, match rectangle 2,3 by

\[
X_2:20;\quad X_0:30;\quad Y_2:31;\quad
\text{another Y}:21.
\]

Thus `y_2=0`, giving `y=y_0<=3`. Equality is forced, as is
`x=8`, and therefore

\[
x_1=3,\qquad x_2=2,\qquad y_0=3.
\]

But `Y_0=C(02)` then has private corners `21,23`: none of
A or the X classes contains either. They form a private row pair
in this positive class, contradicting the unconditional row lemma.

### One zero source

Here `x+y=10`, so `x>=6` and `y>=2`.

If the zero is B or `Z_4`, an `X_2` gives rectangle 2,3 by
`X_2:20, X_0:30, Y:21, zero:31`; a `Y_2` gives the analogous
rectangle using zero `20`, `X_0:30`, and another Y at `21`.
Thus `x_2=y_2=0`. But then `x<=6` and `y=y_0<=3`,
contradicting their sum ten.

If the zero is `Z_2`, the first of those constructions gives
`x_2=0`. Hence `x<=6` and `y>=4`; equality is forced, so
`x_1=3` and `y_0=y_2=2`. Rectangle 3,4 is filled by
`X_1:40, X_0:30, Y_2:31, zero:41`.

If the zero is `Z_3`, a `Y_2` gives rectangle 2,3 by
`zero:20, X_0:30, Y_2:31`, and another Y at `21`.
Thus `y_2=0`, so `y<=3` and `x>=7`. Both X branches occur.
Rectangle 2,4 is filled by
`X_2:20, X_1:40, Y_0:21, zero:41`.

### Two or three zero sources

If two zeros match `20,31`, an X at `30` and a Y at `21`
finish rectangle 2,3. Every zero sees at least one of `20,31`;
with at least two copies, failure of this two-position matching
means that they all miss row 2 or all miss row 3. Thus they are
all `Z_2`, or all `Z_3`.

Both types see `40,41`. Two zeros at those positions, together
with `X_2:20` and a Y at `21`, exclude `x_2>0`. Similarly
using `X_0:30,Y_2:31` excludes `y_2>0`. Hence `x_2=y_2=0`.
The equation `3+x_1+y_0=11-z>=8` forces `x_1>=2`.

For zeros all `Z_2`, match rectangle 3,4 by
`X_1:40, X_0:30`, and two zeros at `31,41`.
For zeros all `Z_3`, match rectangle 2,4 by
`X_1:40, Y_0:21`, and two zeros at `20,41`.
Both give a contradiction.

This proves that `x_0=3` is impossible whenever either X branch
is present. By symmetry, `y_0=3` is impossible whenever either Y
branch is present.

## 4. The original count bounds are restored

We now have

\[
x_0\le2\text{ if }x_1+x_2>0,
\qquad y_0\le2\text{ if }y_1+y_2>0.
\]

Therefore `x,y<=8`; if either branch of a group is absent,
that group's total is at most five. These are the count bounds
used in the original diagonal proof, now established without
an all-private hypothesis. We finish its three zero-count cases,
replacing its final private-corner objections where necessary.

## 5. No zero sources

Here `x+y=11`, so `x,y>=3`. If `x_2,y_2>0`, match rectangle
2,3 by `X_2:20`, another X at `30`, `Y_2:31`, and another
Y at `21`. By symmetry suppose `x_2=0`.

Then `x<=5` and `y>=6`, forcing `y_1,y_2>0`. An `X_1`
would give rectangle 3,4 using `X_1:40`, another X at `30`,
`Y_2:31,Y_1:41`. Thus `x_1=0`. The counts now force

\[
x_0=3,\qquad y_0=2,\qquad y_1=y_2=3.
\]

The positive class `X_0=C(13)` has private corners `30,32`:
A and all three Y classes miss both. This is a forbidden private
row pair. Hence there are no zero-free failures of this form.

## 6. Two or three zero sources

As in Section 3, the `20,31` test forces all zeros to be one
of `Z_2,Z_3`. By symmetry choose `Z_2`.

Two zeros at `40,41` exclude `x_2>0` using rectangle 2,4,
and exclude `y_2>0` using rectangle 3,4. Thus `x_2=y_2=0`.
Now `x,y<=5` and `x+y=11-z` is eight or nine, so `x,y>=3`.
If `x_1,y_1>0`, rectangle 3,4 is supplied by `X_1:40`,
another X at `30`, `Y_1:41`, and a zero at `31`.

If `x_1=0`, the counts force `z=3`, `x_0=3`, and `y=5`.
But the positive class `Z_2=C(34)` has private corners `40,42`,
since A, `X_0,Y_0,Y_1` all miss both. Its three copies have a
forbidden private row pair.

If `y_1=0`, the counts force `z=3`, `y_0=3`, and `x=5`.
Now the positive class `Y_0=C(02)` has private corners
`21,23,24`, all missed by A, `X_0,X_1,Z_2`. Again a triple
has a forbidden private row pair.

## 7. One zero source

Now `x+y=10`, so `x,y>=2`.

If the zero is B or `Z_4`, it sees both rows 2,3. An `X_2`
gives rectangle 2,3 with another X, a Y, and zero `31`; a
`Y_2` gives the symmetric construction. Thus `x_2=y_2=0`,
forcing `x=y=5`. In particular both `X_1,Y_1` occur, and
rectangle 3,4 is matched by `X_1:40`, another X at `30`,
`Y_1:41`, and zero `31`.

Otherwise symmetry makes the zero `Z_2`. An `X_2` again gives
rectangle 2,3, so `x_2=0`, `x<=5`, and `y>=5`. If `y_1,y_2`
are both positive, match rectangle 3,4 by `X:30`, zero `40`,
`Y_2:31,Y_1:41`. Therefore one Y branch is absent, and the
bounds give

\[
x_0=2,\quad x_1=3,\quad y_0=2,
\]

with exactly one of `y_1,y_2` equal to three.

If `y_1=3`, use `X_1:40`, another X at `30`, `Y_1:41`,
and zero `31` for rectangle 3,4.

If `y_2=3`, neither `X_1` nor `Y_2` has any private corner.
For `X_1`, `X_0` covers `10,12,30,32` and `Z_2` covers
`40,42`. For `Y_2`, `Y_0` covers `01,04,21,24`, `Z_2`
covers `31`, and `X_0` covers `34`. The nonprivate-triple
lemma gives both triples own loops, contradicting the
at-most-one-own-loop theorem.

All cases have now been excluded. A non-own-loop triple cannot
have a diagonal private pair. Its two private corners therefore
form a column, as claimed.
