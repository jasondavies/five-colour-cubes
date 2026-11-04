# Four copies of an adjacent class: the other two three-corner covers

This supplements `g4-row-hand.md`. All assertions below are hand matching
arguments in the directed-cut model; the computation was used only to find
the cases. Let `C(S)` denote the cut from `S` to its complement. Fix

\[
A=C(01),\qquad a=4,
\]

and assume every class has at most four copies. A failure cannot have four
copies each of disjoint cuts, or more than seven copies in two cuts sharing
four arcs. In particular, the latter bound will be used for
`P=C(04)` with each of `D=C(034)` and `F=C(024)`.

The four cuts disjoint from `A` are

\[
B=C(234),\quad Z_2=C(34),\quad Z_3=C(24),\quad Z_4=C(23).
\]

Write `z` for their combined multiplicity. We use the established half-array
lemma: four `A`, one cut meeting `A` in a single arc, and any three cuts
disjoint from `A` build an opposite target. Thus `z<=2` whenever a singleton
intersection class is present.

An opposite target written `ab|cd` asks for all eight arcs between its two
pairs, in both directions. A statement assigning several arcs to one
class always uses that many distinct copies.

## 1. Hook cover `{02,03,12}`

Apart from zero-intersection cuts the allowed outside classes are

\[
P=C(04),\quad D=C(034),\quad F=C(024),\quad E=C(134).
\]

Their counts are `p,d,f,e`; all are at most four. Assume `e>0`, since
otherwise the one-row-cover lemma applies. Then

\[
e+p+d+f+z=10,\qquad p+d\le7,\quad p+f\le7.
\]

### Two zero cuts

If one of the two zeros contains colour 3, target `01∣34` works. Use four
`A` for the forward half. Use a `P,D,F` copy for `41`, an `E` for one of
`30,40`, and the two zeros for `31` and the other of `30,40`. The two zeros
can be assigned this way: if the zero used for `31` contains 4, swap their
roles if necessary; a zero missing 3 is exactly `C(24)` and supplies `40`.
Every zero contains at least one of 3 and 4.

If neither zero contains 3, both are `C(24)`. Target `01∣24` uses four `A`
for the forward half and the two zeros, `E`, and a `P,D,F` copy for
`20,21,40,41`, respectively. A `P,D,F` copy exists because `e<=4`.
Consequently `z<=1` in a failure.

### One zero cut

If `d>0`, then `p+f>0`, because otherwise `e+d=9>8`. Target `01∣34`
uses four `A`, then `D` for `31`, a `P,F` for `41`, and `E` and the zero
for `30,40`. Hence `d=0`.

Now `e+p+f=9` and `p+f<=7`, so `e>=2` and `p,f>=1`. If the zero is
`Z_3=C(24)`, target `01∣24` uses four `A`, then zero:`20`, `F:21`,
`E:40`, and `P:41`.

Every other zero contains 3 and supplies `30`. If `f>=2`, target `02∣13`
is given by

| Class | Arcs |
|---|---|
| `A` | `03,12` |
| `E` | `10,32` |
| zero | `30` |
| `F` | `21,23` |
| `P` | `01` |

If `f=1`, necessarily `p=e=4`. Then `P` has a loop: reserve two
same-repeat `P` cubes for its two bicoloured corners, and fill its six
tricoloured corners by remaining `P:01,43`, `A:02,03`, `E:42`, `F:41`.
Four copies of a class force a repeated repeat colour, so this solves.

### No zero cuts

If `e>=2` and `d>=1`, target `01∣34` uses four `A`, two `E` at `30,40`,
one `D` at `31`, and another `P,D,F` at `41`. Thus `e>=2` implies `d=0`
in a failure. Then `e+p+f=10`, so `e>=3` and `p,f>=2`. Target `02∣13`
uses `A:03,12`, `E:10,30,32`, `F:21,23`, `P:01`.

The only remaining possibility has `e=1` and `p+d+f=9`. The bounds
`p+d,p+f<=7` imply `d,f>=2`. A class of size four has a loop, as follows;
the class in the first column has two copies reserved for the bicoloured
corners.

| Reserved class | Its six tricoloured corners |
|---|---|
| `P` | `A:02,03`; `D:42`; `F:43`; remaining `P:01,41` |
| `D` | remaining `D:31,01`; `A:02`; `E:32`; `P:42`; `F:41` |
| `F` | remaining `F:21,23`; `A:03`; `P:43`; two further `P,D:01,41` |

In the last row `p+d=5`, so the further copies exist. The other rows have
all displayed classes present by the preceding count bounds. Thus a
failure would require `p=d=f=3`.

For this last case use the thirteen-cube-core lemma in
`g4-row-hand.md`: `A^4,P^3,D^3,F^3` plus any cut containing one of
`21,31,23,32` solves. Here `E=C(134)` contains `32`.

This proves the hook-cover case.

## 2. Disjoint cover `{02,03,14}`

Use the same `P,D,F`, but now

\[
E=C(123),
\]

with `e>0`; again `e+p+d+f+z=10` and `z<=2`. In addition to `p+d,p+f<=7`
we may assume `p+e<=7`, since `P` and `E` are reverse cuts and four of
each solve an opposite target.

The following small assemblies will be used:

* `2A+2P+2D+F+E` builds `12∣34`: `A:13,14`, `E:24`, `F:23`,
  `D:31,32`, `P:41,42`.
* Interchanging 2 and 3 gives `2A+2P+D+2F+E` building `13∣24`.
* `2A+4D+F+E` builds `12∣34`: `A:13,14`, `E:24`, `F:23`, and `D`
  fills all four reverse arcs. There is a symmetric version with `4F+D`.

### A zero containing 4

If `d>0` and a zero contains 4, target `01∣34` uses four `A`, `E:30`,
zero:`40`, `D:31`, and one further `P,D,F:41`. If `f>0`, use the
colour-swapped target `01∣24`. There is always a further non-`E` copy
because `p+d+f=10-z-e>=4`. Also `d=f=0` would force `p+e>=8`, forbidden.

Therefore any zero in a failure is `Z_4=C(23)`.

### Two copies of `Z_4`

If `e>=2`, use target `14∣23`. Two `A` fill `12,13`, two `E` fill
`24,34`, the two zeros fill `21,31`, and two `P,D,F` fill `42,43`.
These last two arcs can be matched unless `p+d=0` or `p+f=0`; there are
at least four copies in `P,D,F`. In either exceptional case the entire
non-`E` multiplicity is four in `D` or `F`, and `e=4`. These two cuts
are disjoint, so their eight cubes already solve.

If `e=1`, then `p+d+f=7`, whence `p+d,p+f>=3`. At least one of `d,f`
is positive. Suppose `d>0`; the other case is symmetric. Target `14∣23`
uses `A:12,13`, `E:24`, zeros:`34,21`, `D:31`; the remaining sources
match `42,43` because their degrees are at least two and three,
respectively. Thus this case also solves.

### One copy of `Z_4`

If `e>=3`, target `04∣13` uses `E:10,30,34`, `A:14,03`, a `P,F`
copy at `43`, and two further `P,D,F` copies at `01,41`. Here
`p+d+f=9-e>=5`, and `p+f>0` since `d<=4`.

If `e=2`, then `p+d+f=7` and `p+d,p+f>=3`. As in the previous case,
choose `D` if `d>0` (otherwise interchange 2 and 3). Target `14∣23`
uses `A:12,13`, `E:24,34`, zero:`21`, `D:31`, and two remaining
`P,D,F` copies for `42,43`.

If `e=1`, then `p+d+f=8`. Both `d,f` are positive: otherwise a
shared-four-arcs pair has total eight. If `p>=2`, at least one of `d,f`
is at least two, and the corresponding first or second small assembly
above applies. If `p<=1`, at least one of `d,f` equals four, and the
third small assembly or its symmetric version applies.

### No zero cuts

If `e=1`, then `p+d+f=9`; the same small assemblies apply (both `d,f`
are positive, and if `p<=1` one is four).

Suppose `e>=2` and `d,f>0`. Target `14∣23` uses `A:12,13`, `E:24,34`,
`D:31`, `F:21`, and two remaining `P,D,F` at `42,43`. Both last degrees
are positive and their union has at least four copies: indeed
`p+d+f=10-e>=6`, so `p+d,p+f>=2` before removing `D,F`.

Finally suppose, say, `d=0`. Then `e+p+f=10` and `p+e,p+f<=7` give
`e,f>=3`; also `p>0`. Target `04∣13` uses `E:10,30,34`, `A:14`, and
four `P,F` copies for its forward half. Since `p+f=10-e>=6`, this is
possible.

This proves the disjoint-cover case. Together with the one-row lemma,
all three-corner covers without source exceptions are now settled.
