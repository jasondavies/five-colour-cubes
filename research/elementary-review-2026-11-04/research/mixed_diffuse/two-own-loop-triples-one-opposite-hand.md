# Two own-loop triples in a fifteen-pool with one opposite source

**Status: elementary proof.** The proof uses no profile enumeration.

**Theorem.** A failing fifteen-cube pool consisting of fourteen adjacent
sources and one opposite source, with every adjacent tricolour-class
count at most three, has at most one triple class admitting an
own-orientation loop.

An own-orientation loop on a class means that, after reserving two
copies of that class, the remaining sources can match its six
tricoloured corners. The opposite source is allowed in this matching.

This extends `research/pure_supported/two-own-loop-triples-hand.md`.
The constructions below are included to identify precisely the two
points requiring modification when the opposite source can be used
in an asserted loop.

## 1. The possible classes and repeated colours

An own-loop triple in a failure must use all three allowed repeated
colours. Otherwise two copies with the same repeated colour supply
the two bicoloured target corners and the loop completes the target.

An own-loop class `U` conflicts with every present adjacent class `V`
whose pole pair meets that of `U`. To see this, reserve one `U` and
one `V` with a shared repeated colour. For the tricoloured matching,
start with the own-loop matching after two `U` reservations, restore
one universal `U`, and remove the chosen `V`. If the latter was used,
the restored `U` replaces it. This argument remains valid if an
opposite source occurs in the matching.

Consequently two own-loop triples must have disjoint pole pairs:
their three-element repeated-colour sets intersect, so intersecting
pole pairs would give an assembly. A reverse-orientation class with
the same poles as either triple is also absent.

Normalize the first class to `A=C(01)` and the second pole pair to
`23`. The second class is either `B=C(23)` or `C=C(014)`. The `A`
triple uses repeats `2,3,4`; the second triple uses `0,1,4`.

Any further adjacent pole pair must meet at most one of `01,23`.
If it met both, its repeated colour would have to belong to both
disjoint pairs. Hence the eight other adjacent helpers have poles

\[
04,\quad14,\quad24,\quad34,
\]

with forced repeated colours respectively

\[
1,\quad0,\quad3,\quad2.
\]

There is one additional opposite source, denoted `O`.

## 2. The disjoint orientation `B=C(23)`

Consider target `01|23`. Three `A` can fill any three positions of
its forward half, and three `B` can fill any three positions of its
reverse half. Each of the eight possible adjacent helper classes
meets exactly one of these halves. Choose any helper and use it in
the half it meets.

The opposite source `O` meets both halves. Indeed its intersection
with `A` meets at least two of `A`'s three columns, hence it meets
the forward rectangle on columns `2,3`; its symmetric directed
corner set also meets the reverse rectangle. Use `O` in the other
half and fill the remaining positions with the three copies of
each anchor. This gives an opposite assembly.

## 3. The nested orientation `C=C(014)`

Name the eight helper classes as follows.

| Poles | Class | Reverse class | Forced repeat |
|---|---|---|---:|
| `04` | `P=C(04)` | `Pbar=C(123)` | 1 |
| `14` | `Q=C(14)` | `Qbar=C(023)` | 0 |
| `24` | `R=C(24)` | `Rbar=C(013)` | 3 |
| `34` | `S=C(34)` | `Sbar=C(012)` | 2 |

Call `P,Q,Rbar,Sbar` the main classes and the other four the outer
classes. Write

\[
a=g(Pbar)+g(Qbar),\qquad b=g(R)+g(S).
\]

### Three elementary restrictions

**First, `a,b<=3`.** The `Pbar,Qbar` sources are disjoint from `C`,
and `R,S` are disjoint from `A`. Three copies of any adjacent class,
four sources disjoint from it, and one opposite source always solve:
the four disjoint sources match the reverse half of some two-column
rectangle, and the opposite source plus the three class copies fill
the forward half. This is Construction III in
`five-class-mixed-hand-proof.md`, Section 2. Thus four sources in
either outer block would solve.

**Second, a main class of size three excludes every outer source.**
For `P^3`, the two tricoloured corners outside its four-corner
intersection with `C` are `01,41`. Each of `Qbar,R,S` supplies one
of these. Reserve two `P` for the bicoloured corners of a `P` target;
they have the same forced repeat. The remaining `P` and the outer
source fill `01,41`; three `C` and one `A` fill `02,03,42,43`.

If a `Pbar` occurs instead, reserve one `P` and one `Pbar`, which
have the same repeated colour and pole pair. The remaining two `P`
fill `01,41`, and the same four-corner completion applies.

The other main classes follow by interchanging `0,1`, interchanging
`2,3`, and reversing all cuts followed by `(0 2)(1 3)`. The last
symmetry exchanges the two anchors, the two main blocks, and the
two outer blocks.

**Third, if both main blocks occur, every main count is at most one.**
Suppose `P` occurs twice and `Rbar` occurs. Reserve the `A` cube
repeating 3 and an `Rbar` for the bicoloured corners of a `P` target,
using poles `0` and `4`. Two `P` fill `01,41`; three `C` and a
remaining `A` fill `02,03,42,43`. For `Sbar`, reserve the `A` cube
repeating 2. Replacing `P` by `Q` is symmetric.

Conversely, if `Rbar` occurs twice and `P` occurs, reserve the `C`
cube repeating 1 and a `P` for the bicoloured corners of an `Rbar`
target, using poles `2` and `4`. Two `Rbar` fill `32,34`; three `A`
and a remaining `C` fill `02,04,12,14`. The other choices follow
by the same symmetries.

### There is an outer source, and only two outer types

There must be an outer source. Otherwise all eight adjacent helpers
belong to the main classes. If just one main block is present, its
two classes have total capacity at most six. If both blocks are
present, the third restriction bounds their total by four. Neither
can accommodate eight helpers.

This count replaces the own-loop argument used for a pure pool; in
particular it does not assume that either loop avoids `O`.

The presence of an outer source bounds each main class by two. If
both main blocks occur, each is at most one. Either way the main
total is at most four. Thus

\[
a+b\ge4,\qquad a,b\le3.
\]

Both outer blocks therefore occur. On the reverse half of target
`01|23`, their corner pairs are

| Class | Positions |
|---|---|
| `Pbar` | `20,30` |
| `Qbar` | `21,31` |
| `R` | `20,21` |
| `S` | `30,31` |

If three of these four types occur, their at least four copies match
the reverse square. Each position has a neighbour; two positions
see at least two sources; and any three positions see every source.
Three `A` and one `C` fill the forward square. Hence a failure has
just one outer type in each block. Normalize them to

\[
Pbar^a,\quad R^b,\qquad 1\le a,b\le3,\quad a+b\ge4.
\]

### The numerical tail

Write `p,q,rbar,sbar` for the main counts. Their sum is `8-a-b`,
between two and four. By the anchor-exchange symmetry, assume the
block `{Rbar,Sbar}` is present.

If `a>=2` and `sbar>0`, target `04|23` has the assignment

\[
A:02;\quad C:03,42,43;\quad Pbar:30,34;\quad
R:20;\quad Sbar:24.
\]

Otherwise use target `13|24`. Its forward positions can be filled by

\[
A:12,14;\quad Rbar:32;\quad Pbar:34.
\]

A `C` fills reverse position `43`; three `R` fill `21,23,41`.
Alternatively, two `R` fill `21,23` and a `P` fills `41`.

If `a=1`, then `b=3` and the main total is four. Here `Rbar` is
present: without it a single main block has capacity two, while
two present blocks have total capacity at most three. Thus the
displayed `13|24` assignment with three `R` applies.

The remaining case has `a>=2` and `sbar=0`, hence `rbar>0`. If
`P,Q` are absent, the main total is at most two, forcing `a=b=3`;
again use three `R`. If `{P,Q}` is present, every main count is at
most one. Therefore `a+b>=5` and `b>=2`. For `b=3`, three `R`
finish. For `b=2`, necessarily `a=3` and `p=q=rbar=1`, so use two
`R` and the `P`.

All displayed assemblies in this numerical tail use only adjacent
sources. We have reached a contradiction in both orientations,
proving the theorem.

## 4. Consequence for a pure fourteen-cube predecessor

Suppose an adjacent fourteen-pool is failing and has an own-loop
triple. Add one opposite source. If the enlarged fifteen-pool still
fails, the added source cannot meet either private corner of any
other triple having exactly two private corners: the promotion
lemma in `research/pure_supported/private-pair-promotion-hand.md`
would create a second own-loop triple, contrary to this theorem.

This conclusion requires exactly two private corners for the
promoted triple. This note does not establish that every other
triple in a unique-own-loop predecessor has exactly two private
corners, nor does it exclude an opposite source avoiding all such
private pairs. Those are separate remaining structural questions.
