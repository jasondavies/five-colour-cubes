# Two own-loop triple classes cannot occur in a failure

**Theorem.** A failing pure fourteen-cube pool with all tricoloured-class
counts at most three has at most one three-copy class admitting an
own-orientation loop.

An own-orientation loop on a class means that, after removing two copies
of that class, the remaining cubes match its six tricoloured corners.
This proof is elementary and independent of the exploratory own-loop
profile enumeration.

## 1. Repeated colours and the available pole pairs

An own-loop triple must use all three possible repeated colours;
otherwise a same-repeat pair completes its own target.

If `U` has an own loop, it conflicts with every present class `V` whose
pole pair meets that of `U`. Indeed, to reserve one `U,V` for an `U`
target, start with the loop matching after two `U` reservations, restore
one universal `U`, and remove the chosen `V`. If the removed `V` had
been used, the restored `U` replaces it.

Consequently two own-loop triples must have disjoint pole pairs. Their
three-element repeat sets overlap, so intersecting pole pairs would
already give a solution. A reverse-orientation class with the same
pole pair as an own-loop triple is absent for the same reason.

Normalize the two pole pairs to `01` and `23`, and the first class to

\[
A=C(01).
\]

The second class is either `C(23)` or `C(014)`. Both triples use all
three repeats: `A` uses `2,3,4`, while the other class uses `0,1,4`.
Every other present pole pair must meet at most one of `01,23`.
If it met both, its repeat would have to lie in both disjoint pairs.
Thus all eight remaining cubes have one of the four pole pairs

\[
04,\quad14,\quad24,\quad34.
\]

Their repeated colours are forced, respectively, to be

\[
1,\quad0,\quad3,\quad2.
\]

## 2. The second class is `C(23)`

Consider opposite target `01|23`. Each of the eight possible remaining
classes meets exactly one of its two four-corner halves. If a source
of each kind occurs, use those two sources, three `A`, and three
`C(23)` to fill the target.

Otherwise all remaining sources meet the same half. If they meet the
forward half, their only possible corners in the `C(23)` target are
`24,34`; if they meet the reverse half, their only possible corners in
the `A` target are `04,14`. After reserving two copies of the relevant
anchor, its one remaining universal copy and these two corner positions
cannot supply six corners. One of the asserted own loops is impossible.

Thus this orientation always solves.

## 3. The nested orientation `C=C(014)`

Name the eight other classes as follows. A bar denotes the reverse cut.

| Pole pair | Class | Reverse class | Forced repeat |
|---|---|---|---:|
| `04` | `P=C(04)` | `Pbar=C(123)` | 1 |
| `14` | `Q=C(14)` | `Qbar=C(023)` | 0 |
| `24` | `R=C(24)` | `Rbar=C(013)` | 3 |
| `34` | `S=C(34)` | `Sbar=C(012)` | 2 |

Call `P,Q,Rbar,Sbar` the main classes and the other four the outer
classes. Put

\[
a=g(Pbar)+g(Qbar),\qquad b=g(R)+g(S).
\]

### Three preliminary observations

**First, `a,b<=3`.** An own-loop triple has at least five tricoloured
corners met by outsiders. Four sources disjoint from it would give an
opposite assembly: choose two reverse rows each met by at least two of
the four zero sources; they fill that reverse rectangle, and some
outsider meets its forward rectangle because the outside support has
at least five of the anchor's six corners. That outsider and three
anchor copies fill the forward rectangle.

The only permitted classes disjoint from `A` are `R,S`, and the only
permitted classes disjoint from `C` are `Pbar,Qbar`. Hence `a,b<=3`.

**Second, a main class of size three excludes every outer source.**
By symmetry it suffices to consider `P^3`. Its two corners outside the
four-corner intersection with `C` are `01,41`. A `Qbar`, `R`, or `S`
supplies one of these. Reserve a same-repeat `P` pair, use its remaining
copy for the other corner, and use three `C` and one `A` for
`02,03,42,43`. This assembles a `P` target.

If a `Pbar` instead occurs, it has the same forced repeat as `P` and
the same poles. Reserve one `P` and one `Pbar`; the two remaining `P`
fill `01,41`, and the same four-corner completion works.

The needed symmetries are interchange of 0 and 1, interchange of 2 and
3, and reversal followed by `(0 2)(1 3)`. The last symmetry exchanges
`A,C`, exchanges the blocks `{P,Q}` and `{Rbar,Sbar}`, and exchanges
the two outer blocks.

**Third, if both main blocks are present, every main count is at most
one.** For example, if `P` occurs twice and `Rbar` occurs, reserve an
`A` cube repeating 3 and that `Rbar` for the poles `04` of a `P` target.
Two `P` fill `01,41`; three `C` and one remaining `A` fill
`02,03,42,43`. The same construction works with `Q`, or with `Sbar`
instead of `Rbar`.

Conversely, if `Rbar` occurs twice and `P` occurs, reserve the `C`
cube repeating 1 and `P` for an `Rbar` target's poles `24`. Two `Rbar`
fill `32,34`; three `A` and one remaining `C` fill
`02,04,12,14`. Again the other choices are symmetric.

### The outer sources have only two types

There must be an outer source. If there were none, the own loop on
`A` would require some `Rbar,Sbar`, since its corners `04,14` cannot
both be filled by its one remaining copy. Similarly the own loop on
`C` would require some `P,Q` to supply `42,43`. Both main blocks would
then be present, forcing at most one of each main class, whereas eight
sources are required.

Since an outer source is present, the second observation bounds every
main class by two. If both main blocks occur, the third observation
improves this to one. Either way, the main total is at most four.
Thus

\[
a+b\ge4,\qquad a,b\le3,
\]

so both outer blocks are nonempty.

For target `01|23`, the reverse intersections of the outer classes are

| Class | Reverse positions |
|---|---|
| `Pbar` | `20,30` |
| `Qbar` | `21,31` |
| `R` | `20,21` |
| `S` | `30,31` |

Any three of these four types, with at least four copies in total,
match the four positions. This follows directly from Hall: each
position has a neighbour, any two positions see at least two sources,
and any three positions see every source. Three `A` and one `C`
fill the forward half. Therefore at most two outer types can occur.
Since both outer blocks are nonempty, exactly one occurs in each.
By interchanging 0,1 and 2,3, normalize them to

\[
Pbar^a,\quad R^b,\qquad 1\le a,b\le3,\quad a+b\ge4.
\]

### The remaining numerical cases

Write `p,q,rbar,sbar` for the main counts. Their sum is `8-a-b`,
between two and four. By the exchange symmetry above, assume the
block `{Rbar,Sbar}` is present.

If `a>=2` and `sbar>0`, target `04|23` is filled by

\[
A:02;\quad C:03,42,43;\quad Pbar:30,34;\quad
R:20;\quad Sbar:24.
\]

Otherwise consider target `13|24`. Its forward half is filled by

\[
A:12,14;\quad Rbar:32;\quad Pbar:34.
\]

A `C` fills `43`; three `R` can fill its other reverse positions
`21,23,41`. Two `R` also suffice if a `P` supplies `41`.

If `a=1`, then `b=3` and the main total is four. Here `Rbar` must be
present: without it, a single main block has capacity two, while two
present blocks have total capacity at most three. Thus the displayed
target works with three `R`.

The only remaining case has `a>=2` and `sbar=0`, hence `rbar>0`.
If `P,Q` are both absent, the main total is at most two, forcing
`a=b=3`, and three `R` finish. If the block `{P,Q}` is present, every
main count is at most one; therefore `a+b>=5` and `b>=2`. When `b=3`
we again finish with three `R`. When `b=2`, necessarily `a=3` and
`p=q=rbar=1`; use two `R` at `21,23` and the `P` at `41`.

All cases have an opposite or adjacent assembly. Two own-loop triple
classes are therefore impossible in a failure.

## 4. The same exclusion for fifteen cubes

The argument also excludes two own-loop triple classes in a failing
pure fifteen-cube pool with class counts at most three. The disjoint-
outset orientation is handled exactly as in Section 2.

For the nested orientation there are now nine star-class helpers.
Every preliminary observation remains valid: `a,b<=3`, an outer
source exists, each main count is at most two, and the main total is
at most four. Consequently `a+b>=5`. The reverse-square argument
again reduces the outer sources to `Pbar^a,R^b`. Now

\[
2\le a,b\le3,\qquad
m=p+q+rbar+sbar=9-a-b\in\{3,4\}.
\]

By the exchange symmetry assume the `Rbar,Sbar` block is present.
If `sbar>0`, the displayed `04|23` assembly applies, since `a>=2`.
Otherwise `rbar>0`. The `P,Q` block cannot be empty, since the main
total is at least three but `rbar<=2`. Both blocks therefore occur,
so each main count is at most one. With `sbar=0`, this forces

\[
m=3,\quad a=b=3,\quad p=q=rbar=1.
\]

The displayed `13|24` assembly, using three `R`, now solves. This
proves the fifteen-cube extension independently of any classification
of fourteen-pools with a unique own-loop triple.
