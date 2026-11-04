# A nonlooped three-copy class has two private corners

**Theorem.** In a failing pure fourteen-cube pool whose tricoloured
classes have multiplicity at most three, every three-copy class without
a loop has at least two tricoloured corners absent from all other
classes. In fact, it suffices that the class has no loop using its own
cut orientation.

This proof uses the explicit matching lemmas in `g4-row-hand.md`,
`g4-hook-disjoint-hand.md`, and `g4-exception-hand.md`. It does not use
the exhaustive lists of fourteen-cube failures.

## 1. Hall covers and four zero cuts

Normalize the three-copy class to `A=C(01)`, and suppose at most one
of its six corners is private. Thus its eleven outsiders meet at least
five corners of the two-by-three array `02,03,04;12,13,14`.

Call a cut disjoint from `A` a zero cut. The zero classes are
`B=C(234)` and `Z_i=C({2,3,4}\setminus{i})`, for `i=2,3,4`.

If four zero cubes are present, choose two colours `q,s` each contained
in at least two of their outsets. This is always possible: at most one
of the three `Z_i` multiplicities exceeds two. Their four cubes match
`q0,q1,s0,s1`, since each row has degree at least two and their union
sees all four sources. Some outsider meets the forward half
`{0q,0s,1q,1s}`: otherwise all outsider intersections with `A` would
lie in the other column, contradicting the five-corner hypothesis.
Use that outsider once and three `A` copies for the forward half.
This gives an opposite target. Consequently the zero count satisfies

\[
z\le3.
\]

After removing two `A` cubes for bicoloured corners, one `A` remains.
If the outsiders match five `A` corners, that last `A` completes the
sixth and gives a loop. Their matching rank is therefore at most four.
By Konig's theorem they admit a cover by `c` corner vertices and at
most `4-c` source copies.

* `c=4` with no source exceptions would make at least two corners
  private, contrary to the hypothesis.
* `c=0` leaves at least seven zeros, impossible.
* `c=1` leaves at least eight sources in one singleton-intersection
  class and the zero classes; these have total capacity at most `3+3=6`.

Thus it remains to examine three corners plus one exceptional source,
or two corners plus two exceptional sources.

## 2. The fourth-anchor substitution

The following observation allows the four-copy proofs to be reused.
If a cut `R` meets `A` in at least two columns, then for every pair
`q,s` from `{2,3,4}`, it meets the forward half of target `01|qs`.
Hence three `A` and `R` can replace four `A` whenever those four copies
were used to fill that forward half.

The intersections of a cut with `A` are empty, a single cell, a pair
in one row, a two-by-two rectangle, or the full array. Therefore any
exceptional cut contributing at least two new cells has the required
two-column property.

## 3. Three-corner cover, one exceptional source

The other ten outsiders have their intersections within three cells.
The exceptional source `R` contributes at least two additional cells,
by the five-corner hypothesis. Up to symmetry the three-cell cover is
a row, a hook, or a disjoint pair-and-singleton.

### Row cover

Normalize the row to `02,03,04`. Then `R` contains two corners of the
other row. The ten normal outsiders are exactly the `P_i,D_i` and zero
classes of `g4-row-hand.md`, now all of capacity three.

The opposite-target arguments in Section 1 of that note still work:
each use of four `A` was a forward half of `01|qs`, so use three `A`
and `R`. Thus `z<=1`. Section 2 is unnecessary, since the class cap
three is already assumed. Section 3 uses only two `A` and reduces the
normal counts to the same Families I and II.

Every completion and conflict in Family I uses at most three `A`, so
its repeated-colour contradiction applies unchanged. In Family II,
the only use of four `A` is to fill the three second-row corners and
one first-row corner in an `A` target. `R` fills one of its second-row
corners and the three `A` fill the other three positions. The same
two looped three-copy classes are therefore joined and require six
different repeated colours. This settles the row cover.

### Hook cover

Normalize the cover to `{02,03,12}`. Its nonzero normal classes are

\[
P=C(04),\quad D=C(034),\quad F=C(024),\quad E=C(134).
\]

If `e=0`, the row argument just proved applies. Otherwise
`p+d+f+e+z=10`, with all four counts at most three. The possible
exceptional cuts adding at least two cells outside the hook are

\[
R=C(12),\quad C(013),\quad C(012).
\]

The two-zero and one-zero arguments of the hook proof in
`g4-hook-disjoint-hand.md` transfer directly whenever four `A` fill
a target `01|qs`: replace one by `R`. For completeness, the count
reduction is particularly short here. Two zeros already solve by
that matching argument. With one zero, `d>0` gives target `01∣34`;
if `d=0`, then `e=p=f=3`. For zero `Z_3`, target `01∣24` solves;
every other zero supplies `30` in target `02∣13`, whose other seven
positions are `A:03,12`, `E:10,32`, `F:21,23`, `P:01`.

With no zeros, `e>=2` implies `d>0` because the other three counts
could otherwise sum to at most nine. Target `01∣34` then uses the
four-anchor substitution and `E:30,40`, `D:31`, and another
`P,D,F:41`. The only remaining case is `e=1,p=d=f=3`. Its three
possible exceptional sources give these opposite assemblies:

| Exceptional `R` | Target | Assignment |
|---|---|---|
| `C(12)` | `01∣24` | `A:04,12,14`; `P:02`; `R:20`; `F:21`; `E:40`; `D:41` |
| `C(013)` | `13∣24` | `A:12,14`; `D:32`; `R:34`; `F:21,23,41`; `P:43` |
| `C(012)` | `12∣34` | `A:13,14`; `F:23`; `R:24`; `D:31,32,41`; `P:42` |

Thus the hook cover is impossible.

### Disjoint cover

Normalize the cover to `{02,03,14}`. Use the same `P,D,F` but now
`E=C(123)`. If `e=0`, use the row case. Otherwise the disjoint-cover
proof in `g4-hook-disjoint-hand.md` applies with the fourth-anchor
substitution. Every use of four `A` in that proof fills the forward
half of a target `01|qs`; all other assemblies use at most three `A`.
Its initial half-array lemma also has that forward-half form. All
count bounds remain valid, since the present cap three is stronger
than its cap four. Thus the disjoint cover also gives an assembly.

## 4. Two-corner cover, two exceptional sources

There are nine normal outsiders. If either exception adds at most one
cell outside the two-corner cover, add that cell to the corner cover;
there is then a three-corner cover with only one source exception,
already settled. We can therefore suppose both add at least two cells.

### Corners in different rows

For a column, normalize to `{02,12}`. The only nonzero normal classes
are `D=C(034), E=C(134)`. Since `d+e+z=9` and each of these three
terms is at most three, all are three. Target `01∣34` needs four
forward sources and `D:31,41`, `E:30,40`. The five-corner hypothesis
guarantees that at least one exception has a forward corner outside
column 2; use it with three `A` to complete the forward half.

For a diagonal, normalize to `{02,13}`. The singleton classes
`D=C(034), E=C(124)` again each occur three times. Target `03∣12`
is filled by `A:02,13`, `D:01,31,32`, `E:10,20,23`.

### Corners in the same row

Normalize to `{02,03}`. The normal nonzero classes are
`P=C(04),D=C(034),F=C(024)`, with

\[
p+d+f+z=9,\qquad p,d,f\le3.
\]

Both exceptions `R,S` contain a pair of second-row corners, because
they each add at least two cells outside `{02,03}`. At least one of
`D,F` is present, since otherwise `p+z<=6`. The half-array lemma
with three `A`, the fourth-anchor substitute `R`, a singleton source,
and three zero sources shows that `z<=2`.

The proof now follows the same small conflict clique as in
`g4-exception-hand.md`, with these explicit adjustments:

* `P` has a loop whenever `p,d,f>=2`: reserve two `P`, then use
  `A:02,03`, `D:01,42`, `F:41,43`.
* To join `A` to `P,D`, or `F`, use an `A` target. After reserving
  one cube from each endpoint, two `A` remain. Normal sources fill
  `02,03`; the exceptions fill two different second-row corners,
  possible because each sees two such corners; two `A` finish.
* To join `P,D` or `P,F`, use an `A` target again. Two normal sources
  fill `02,03`; one exception fills a second-row corner and the three
  `A` finish.
* If one of `D,F` occurs three times, their edge is witnessed exactly
  as before: for `f>=3`, reserve one `D,F` and use remaining
  `F:21,23`, `P:01,43`, remaining `D:41`, and `A:03`.

If `z=0`, then `p=d=f=3`; the clique `A,P,D,F`, with `P` looped,
requires `1+3+1+1=6` different repeats. If `z=1`, the counts are a
permutation of `2,3,3`. The same contradiction applies when `p=3`.
When `p=2`, the zero contains 2 or 3, so it loops `F` or `D` as in
the earlier note, and the clique `A,P,F` or `A,P,D` requires
`1+2+3=6` repeats.

If `z=2`, the forward-half argument from that note gives an opposite
assembly unless the two zeros are identical and one of `d,f` is zero.
But then `p+d+f=7` would have only two nonzero counts, contradicting
the cap three. So this final case solves as well.

All possible Hall covers have led to an assembly. The assumed
three-copy nonlooped class must therefore have at least two private
tricoloured corners.
