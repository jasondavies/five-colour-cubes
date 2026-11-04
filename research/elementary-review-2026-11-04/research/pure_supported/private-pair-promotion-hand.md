# A source meeting a private corner promotes a triple to an own loop

**Matching lemma.** In a failing pure fourteen-cube pool with class
multiplicities at most three, suppose a triple class has exactly two
private tricoloured corners. Its other four tricoloured corners can be
matched by four distinct cubes from other classes.

**Promotion corollary.** Adding any cube whose tricoloured corners
include either private corner makes this triple class completable in
its own orientation after two copies are reserved. In particular, an
added opposite-repeat cube meeting a private corner creates an own loop.

## 1. The possible Hall cover

Normalize the triple to `A=C(01)`. Its eleven outsiders meet exactly
four of its six tricoloured corners. Call a source disjoint from `A`
a zero source, and write their number as `z`.

There are at most three zero sources. Indeed any four zero cuts have
a matching on two full reverse rows `q0,q1,s0,s1`: choose two rows each
seen by at least two of the sources. Their union sees all four sources.
The corresponding four-corner forward half cannot consist entirely
of private corners, since `A` has only two private corners. An outsider
therefore supplies one forward corner, and three `A` supply the other
three, giving an opposite assembly.

Thus at least eight outsiders meet `A`. Suppose they cannot match its
four nonprivate corners. Their matching rank is at most three, so by
Konig's theorem their incidences have a cover consisting of `c` corner
vertices and at most `3-c` source vertices.

* Three corner vertices and no source exceptions cannot cover four
  occupied corners.
* One corner and two source exceptions cover at most five nonzero
  sources: the unique singleton-intersection class has capacity three.
  Zero corners cover at most three sources.
* Two corners in different rows allow only their two singleton classes,
  with combined capacity six, plus one exception. This is again fewer
  than eight sources.

The only possibility is two corners in one row and one exceptional
source. Normalize these corners to `02,03`. The ordinary nonzero
classes are

\[
P=C(04),\quad D=C(034),\quad F=C(024).
\]

If their counts are `p,d,f`, and the exceptional source is `E`, then

\[
p+d+f+z=10,\qquad p,d,f\le3,\qquad z\le3.
\]

Consequently `1<=z<=3`, and all three ordinary classes are present.
The exceptional source supplies exactly two new `A` corners. It is
therefore one of `C(12),C(13),C(14),C(014)`. In particular, it meets
two second-row columns of `A`, and meets the forward half of every
target `01|qs` with `q,s` in `{2,3,4}`. Thus three `A` and `E` can
fill any such forward half.

## 2. Two or three zero sources give an opposite assembly

Choose any two zeros. If they can fill `20,30`, use `F:21,D:31` to
complete the reverse half of target `01|23`.

Otherwise the two zeros must both omit row 2 or both omit row 3:
each zero sees at least one of these rows, and two nonempty neighbour
sets fail a two-position matching only when they are the same singleton.

If both zeros are `C(34)`, let them fill `30,40`, and use `D:31,P:41`
for target `01|34`. If both are `C(24)`, use them at `20,40` and use
`F:21,P:41` for target `01|24`.

In every case three `A` and `E` fill the forward half. Hence `z>=2`
is impossible in a failure.

## 3. One zero source gives a repeated-colour contradiction

Now `z=1`, so necessarily `p=d=f=3`.

The class `P` has an own loop. After reserving two `P`, match its
tricoloured corners by

\[
A:02,03;\quad D:01,42;\quad F:41,43.
\]

The zero source contains 2 or 3. If it contains 3, `D` also has an
own loop: after reserving two `D`, use

\[
\text{remaining }D:32;\quad \text{zero}:31;\quad A:02;
\quad P:41,42;\quad F:01.
\]

If the zero contains 2, interchange 2 and 3 to obtain a loop on `F`.

The looped classes `P,D` are joined. If they share a repeated colour,
reserve one of each for an `A` target's bicoloured corners, using pole
0 from `P` and pole 1 from `D`. A remaining `P` fills `02`, an `F`
fills `03`, and `E` fills one second-row corner; three `A` fill the
other positions. The same argument joins `P,F`.

Each looped triple needs three different repeated colours, while the
joined triples must have disjoint repeat sets. Six colours would be
required. This is impossible, completing the matching lemma.

## 4. Promotion by an added source

Let the private corners be `u,v`. Reserve two cubes of the triple.
If an added source supplies `u`, use it there, use the remaining cube
of the triple at `v`, and use the four outside matches just proved for
the other corners. This is an own-orientation loop.

If another own-loop triple is already present and its pole pair meets
that of the promoted triple, an assembly follows immediately: both
triples must otherwise use all three possible repeated colours, their
repeat sets overlap, and the universal-restoration argument joins them.
This last conclusion remains valid when the added source is opposite-
repeat; it is used only for a tricoloured position.
