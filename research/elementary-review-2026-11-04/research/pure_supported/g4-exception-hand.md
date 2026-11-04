# Four copies of an adjacent class: covers with source exceptions

This completes the pure fourteen-cube case with a tricoloured class of
size four, assuming the established bound that no class has more than
four copies. The three-corner covers are handled in `g4-row-hand.md` and
`g4-hook-disjoint-hand.md`.

## Normal form and a useful zero-cut lemma

Write `C(S)` for the directed cut from `S` to its complement in
`{0,1,2,3,4}`. Fix `A=C(01)` with four copies. Its six arcs form the
two-row, three-column array

\[
\{02,03,04;12,13,14\}.
\]

The cuts disjoint from `A` are `B=C(234)` and `Z_i=C({2,3,4}\setminus{i})`
for `i=2,3,4`. Call their combined count `z`.

**Four-zero lemma.** Four `A` and any four zero cuts build an opposite
target. Choose two colours `q,s` in `{2,3,4}` each contained in at least
two of the four zero outsets. Such a choice exists because at most one
of the three counts of `Z_i` exceeds two. Every zero contains `q` or `s`.
Hence their four copies match `q0,q1,s0,s1`: each row has degree at least
two and the union of the rows sees all four copies. Four `A` fill the
forward half of target `01|qs`.

Thus `z<=3` in a failure. We also use the established half-array lemma
that four `A`, a cut meeting `A` in one arc, and any three zero cuts
build an opposite target. If a singleton-intersection class is present,
then `z<=2` in a failure.

Two of the four `A` copies have the same repeated colour. Reserve them
for the bicoloured corners of their own target. If the ten outsiders
have matching rank at least four on the six arcs of `A`, four of them
and the remaining two `A` complete the target. Therefore their rank is
at most three. By Konig's theorem, they admit a cover by `c` corner
vertices and at most `3-c` individual source copies.

For `c=0` or `1`, removing at most three or two source copies leaves at
least seven zeros, or at least eight copies in one singleton class and
the zero classes. The former contradicts `z<=3`; the latter contradicts
the sum of the bounds four and three. Thus only `c=2,3` remain.

## Two-corner covers in different rows

If the two corners lie in a column, normalize them to `{02,12}`. Apart
from one exceptional source, the outsiders are zero cuts and the two
singleton classes `D=C(034), E=C(134)`. Their counts satisfy `d+e+z=9`.
There is a singleton class, so `z<=2`; thus `d,e>=3`. But target
`01∣34` is filled by four `A`, `D:31,41`, and `E:30,40`.

If the two corners are in distinct columns, normalize them to `{02,13}`.
The two singleton classes are now `D=C(034), E=C(124)`, again with
`d,e>=3`. Target `03∣12` is filled by `A:02,13`, `D:01,31,32`, and
`E:10,20,23`.

Consequently a cover with a source exception must have its two corners
in the same row.

## Two corners in one row

Normalize the corners to `{02,03}`. The nonzero normal classes are

\[
P=C(04),\quad D=C(034),\quad F=C(024),
\]

with counts `p,d,f`. There is one exceptional cube `E`, and

\[
p+d+f+z=9,\quad p,d,f\le4,\quad p+d,p+f\le7.
\]

The last inequalities follow from the shared-four-arcs bound. There is
at least one `D` or `F`: otherwise `p+z=9` contradicts `p<=4,z<=3`.
Thus `z<=2`.

If `E` contributes at most one corner outside `{02,03}`, all outsiders
have a three-corner cover, already settled. Otherwise, up to swapping
2 and 3, `E` is one of

\[
C(14),\quad C(12),\quad C(014),\quad C(013).
\]

These are respectively an aligned opposite-row pair, a skew opposite-row
pair, an aligned four-corner rectangle, and a skew rectangle. In
particular, every remaining `E` contains an arc of the second row of `A`.

### Completion and conflict lemmas

The following statements make the subsequent counting short. A loop on
a class means that any two copies of that class with the same repeated
colour build a target after adding six further cubes. An edge between
two classes means the analogous statement for one reserved cube from
each class. Thus looped classes use distinct repeated colours in a
failure, and joined classes use disjoint sets of repeated colours.

**Heavy-class completions.** Suppose `p,d,f>0` and one count is four.
It has a loop. Reserve two of that class; the following table gives the
six tricoloured corners, using remaining copies.

| Class of size four | Completion |
|---|---|
| `P` | `A:02,03`; `D:42`; `F:43`; remaining `P:01,41` |
| `D` | remaining `D:31,32`; `A:02`; `P:42`; `F:41`; one further `P,F:01` |
| `F` | remaining `F:21,23`; `A:03`; `P:43`; `D:41`; one further `P,D:01` |

The further copy in the last two rows exists since the other two counts
sum to `5-z>=3`. A size-four loop solves by the pigeonhole principle.

**Small conflict clique.** Suppose `p,d,f>=2`, at least one of `d,f`
is at least three, and `E` has a second-row arc of `A`. Then `A,P,D,F`
are pairwise joined, and `P` has a loop.

For the loop on `P`, reserve two `P` and use `A:02,03`, `D:01,42`,
`F:41,43`. To join `A` to any one of `P,D,F`, use target `A`: after
reserving one copy of each endpoint, three `A` remain; two normal
copies fill `02,03` and `E` fills a second-row arc, while the three `A`
fill the other three positions. The endpoint pole pairs permit its
two bicoloured corners: `P` supplies pole 0, and `D,F` supply pole 1.

To join `P,D`, use target `A`, with bicoloured corners supplied at poles
0 and 1. Four `A` remain, and a remaining `P` and an `F` supply `02,03`.
The `P,F` edge is symmetric. Finally, if `f>=3`, use target `F` for
the `D,F` edge: after reserving one of each, fill its tricoloured corners
by remaining `F:21,23`, `P:01,43`, remaining `D:41`, and `A:03`.
If `d>=3` instead, interchange 2 and 3.

In particular, if `p=3` this clique requires at least `1+3+1+1=6`
different repeated colours, impossible with five colours.

If `p=2,d=f=3` and a zero cube is also available, that zero contains
2 or 3. If it contains 3, `D` has a loop: reserve two `D` and fill by
remaining `D:32`, zero:`31`, `A:02`, `P:41,42`, `F:01`.
If it contains 2, the symmetric construction loops `F`. The clique
`A,P,D` or `A,P,F` then requires `1+2+3=6` different repeated colours.

### No zero cubes

Here `p+d+f=9`. The shared-four-arcs bounds imply `d,f>=2`, and `p>=1`.
If any count is four, the heavy-class completion solves. Otherwise all
three counts equal three, and the small conflict clique solves.

### One zero cube

Here `p+d+f=8`, and `d,f>=1`. If `p>0`, a size-four count solves by the
heavy-class completion. Otherwise the counts are a permutation of
`2,3,3`, covered by the small conflict clique and its zero-cube extension.

If `p=0`, then `d=f=4`. There are only the four exceptional source
types listed above:

* If `E=C(14)` or `C(014)`, it contains `42`. Reserve two `D`, then
  use remaining `D:31,32`, `A:02`, `F:01,41`, `E:42`. This is a loop
  on `D`.
* If `E=C(12)`, target `12∣34` uses `A:13,14`, `E:24`, `F:23`, and
  four `D` for all four reverse arcs.
* If `E=C(013)`, target `13∣24` uses `A:12,14`, `E:34`, `D:32`, and
  four `F` for all four reverse arcs.

### Two zero cubes

Four `A` fill the forward half of any target `01|qs`, with `q,s` in
`{2,3,4}`. The two zero cubes fill `q0,s0` unless both are the same
`Z_i` with `i` equal to `q` or `s`. Once these are filled:

* pair `{3,4}` works if `d>0`, using `D:31` and any further `P,D,F:41`;
* pair `{2,4}` works if `f>0`, symmetrically;
* pair `{2,3}` works if `d,f>0`, using `F:21,D:31`.

Since `p+d+f=7`, at least one of `d,f` is positive. If the zeros differ,
or one is `B`, the first or second construction therefore solves.
If both zeros are `Z_2`, failure forces `d=0`; if both are `Z_3`,
it forces `f=0`; if both are `Z_4`, it forces at least one of `d,f`
to vanish. Up to swapping 2 and 3, the only remaining possibility is
`d=0`, `p+f=7`, hence `(p,f)=(4,3)` or `(3,4)`.

For `(4,3)`, `P` has a loop: reserve two `P` and use remaining `P:01,42`,
`A:02,03`, `F:41,43`. For `(3,4)`, `F` has a loop: reserve two `F` and
use remaining `F:21,23`, `A:03`, and `P:01,41,43`.

All source-exception covers are now excluded. Together with the three
corner-cover lemmas, this proves that any pure fourteen-cube pool with
maximum tricoloured-class count four has an assembly.
