# Seven distinct opposite varieties and any adjacent source

**Status: elementary proof.** Seven distinct opposite varieties,
together with any adjacent source, assemble an opposite target.

## 1. Three two-column targets

Let the adjacent class be \(A=C(01)\). Its six corners form the
usual two-by-three grid. Each opposite variety has one of the fifteen
grid patterns: twelve pairs of positions in distinct columns, and
three complete two-column rectangles. Patterns determine varieties
uniquely.

Consider the three opposite targets whose forward halves are the
three two-column rectangles of this grid. If the seven opposite
sources match seven positions of any such target, the adjacent source
fills the last position. Indeed it has exactly one orientation of
each target edge. Reversing every corner in the seven-position
matching, if needed, makes the omitted corner have the required
orientation.

Suppose a two-column target has no seven-position matching. By
source-side Hall, some source subcollection sees too few target
positions. Its union consists of complete bidirected edge pairs.

* One edge pair cannot be deficient: only two opposite varieties have
  that edge as their complete target intersection, and sources are
  distinct.
* Two edge pairs can be deficient only if five sources are confined
  to them. Exactly five opposite varieties have this property, so
  all five must be present.
* Three edge pairs can be deficient only if all seven sources are
  confined to them, meaning that the remaining target edge is
  completely uncovered.
* Four edge pairs cannot be deficient with only seven sources.

We handle the five-variety case first.

## 2. A robust five-source core

Suppose five source patterns project into two positions of one
two-column rectangle. If these two positions are in the same column,
the five source types are exactly the patterns supported on the
rectangle formed by that column and the omitted third column:
the full rectangle and its four two-position patterns.

If the two positions are in different columns, the five types are
the five two-position patterns supported on those positions together
with the two positions in the omitted third column. This four-position
shape has column sizes \(2,1,1\).

In either case there is a central opposite target \(T\) with the
following properties:

1. each of the five source varieties sees at least two edges of \(T\);
2. each target edge occurs in three of the five varieties.

For the rectangle shape, \(T\) is the full-rectangle variety. For
the \(2,1,1\) shape, it is the variety joining the two singleton
positions. The two explicit diagrams in
`six-opposites-three-adjacent.md` establish the second case directly.

These five distinct sources fill any five target positions. A set
using one target edge has three neighbours. A set using two edges
has at least four: among sources seeing at least two target edges,
only the unique variety with the complementary two-edge intersection
can avoid both. A set using at least three target edges sees all five
sources. Hall proves the claim.

The two other opposite sources and the adjacent source can choose
three distinct compatible corners of \(T\). Each sees at least
two corners, so the only possible three-source Hall failure would
put their entire union in the same two corners. Opposite-source
intersections are bidirected, whereas an adjacent source sees corners
on at least two different edges; such a two-corner union is impossible.

Use those three sources at the chosen corners and the robust five-source
core at the remaining five. This assembles the target.

## 3. Uncovered positions cannot block all three rectangles

We may now assume the seven source varieties contain none of the
five-type cores just described. Every failed two-column target must
therefore have an uncovered grid position.

To block all three two-column rectangles, uncovered positions must
occur in at least two different columns: positions in one column
alone do not block the rectangle on the other two columns. Choose
one uncovered position from each of two columns. All seven source
patterns avoid these two positions, so they are supported on the
remaining four positions, of column sizes \(2,1,1\).

But that shape supports only five opposite varieties. It cannot
contain seven distinct source varieties. This contradiction proves
the theorem.

## Consequence

The seven-opposite branch of the capped fourteen-source problem is
settled whenever the seven opposite sources have distinct varieties.
The opposite inventory profiles \(2,1,1,1,1,1\) and
\(2,2,1,1,1\), with nonneighbouring doubled varieties in the latter
case, still need an elementary argument at this checkpoint.
