# Three identical opposite cubes plus the reverse six-cut family

## Statement

Let `O` be the opposite-repeat variety with repeated colour `0` and
opposite-pair partition `{1,2}|{3,4}`. A collection consisting of three
copies of `O` and eleven adjacent-repeat cubes from root classes
`0,3,10,12,15,17` always solves.

These six adjacent classes are exactly the directed cuts containing
the common arc `1 -> 2`. Write them as follows, with counts `a,b,c,d,e,f`:

| Name | Outset | Poles | Root class |
| --- | --- | --- | --- |
| `A_0` | `{0,1}` | `{0,1}` | 0 |
| `A_3` | `{1,3}` | `{1,3}` | 10 |
| `A_4` | `{1,4}` | `{1,4}` | 12 |
| `B_0` | `{1,3,4}` | `{0,2}` | 3 |
| `B_3` | `{0,1,4}` | `{2,3}` | 15 |
| `B_4` | `{0,1,3}` | `{2,4}` | 17 |

We may assume every adjacent class count is at most five, by the
established six-class lemma. No shared-four pair bound is needed below.

## 1. An opposite-target construction forces two zero classes

Consider the opposite target with repeated colour `1` and partition
`{0,2}|{3,4}` (root target 63). Four of its arcs are
`0->3,0->4,3->0,4->0`.

The first pair can be matched from `A_0,B_3,B_4` precisely when

    a+e >= 1,   a+f >= 1,   a+e+f >= 2.             (1)

The second pair can be matched from the disjoint class set
`B_0,A_3,A_4` precisely when

    d+b >= 1,   d+c >= 1,   d+b+c >= 2.             (2)

If both pairs can be matched, reserve these four adjacent cubes.
Every adjacent class except `A_0` supplies at least one of the four
remaining target arcs `2->3,2->4,3->2,4->2`. Since `a<=5`, there
are at least six non-`A_0` cubes; at least two remain after the four
reservations. Use one for any such arc, and use the three copies of
`O` for the other three arcs. This gives a solution.

Hence one of the two blocks fails its two-corner matching. The symmetry
interchanging colours `1,2` and reversing all arrows swaps the blocks,
so suppose (1) fails. Thus

    a+e+f <= 1,   or   a=e=0,   or   a=f=0.         (3)

The first possibility is impossible in a failure. It would give
`b+c+d>=10`, so one of `b,c,d` is at least four. Any such class is
robust in this situation, as the inequalities in the next section
show, and a robust class of size at least four supplies a solution.

Swapping colours `3,4` interchanges the last two possibilities in (3).
We may therefore assume

    a=e=0.                                        (4)

## 2. Robustness leaves just one count pattern

A cut is robust if its six tricoloured corners survive arbitrary
removal of two source cubes. The three copies of `O` are included
in these matching counts. The following are the nonautomatic Hall
conditions for the four classes needed here:

| Class | Conditions for robustness |
| --- | --- |
| `A_3` | `b+d>=3`, `b+f>=3`, `b+c+d>=4`, `b+d+f>=4`, `b+c+d+f>=5` |
| `A_4` | `c+d>=3`, `c+e>=3`, `b+c+d>=4`, `c+d+e>=4`, `b+c+d+e>=5` |
| `B_0` | `b+d>=3`, `c+d>=3`, `b+c+d>=5` |
| `B_4` | `a+f>=3`, `b+f>=3`, `a+b+f>=4`, `a+e+f>=4`, `a+b+e+f>=5` |

These are obtained directly from the six arcs of the indicated cut:
any tested subset meeting `O` has three additional neighbours. The
total-count condition is automatic because there are eleven adjacent
sources. The table also justifies the preceding paragraph when
`a+e+f<=1`.

Under (4), put `Y=b+c+d=11-f>=6`. Any one of `b,c,d` of size at least
four satisfies its row of the table and gives a solution. Thus each
is at most three. If `f=5`, its class is robust. If `f=4`, its class
is robust unless `b=0`, but then `c+d=7` contradicts `c,d<=3`.
Therefore `f<=3` as well.

The four counts `b,c,d,f` sum to eleven and are at most three. Exactly
one equals two and the other three equal three.

## 3. Three placements of the two are impossible by repeat constraints

A robust class of size three in a failure has one copy of each of
its three varieties. If a source's pole pair meets the robust pole
pair in one colour, its repeated colour is forced to be the unmatched
pole of the robust class; otherwise the two corresponding copies
provide that robust target's two bichromatic corners.

If `d=2` or `f=2`, both `A_3,A_4` have size three and are robust.
Their pole pairs `{1,3}` and `{1,4}` meet. One robust class therefore
forces the other to repeat a single colour, contradicting its three
distinct repeats.

If `b=2`, the classes `A_4,B_0` are robust of size three, with disjoint
pole pairs `{1,4}` and `{0,2}`. Every `B_4` copy, with poles `{2,4}`,
would have to repeat `1` because of `A_4`, and repeat `0` because of
`B_0`. This is impossible.

It remains that

    (b,c,d,f) = (3,2,3,3).

## 4. The final forced case has an explicit eight-cube solution

Now `A_3,B_0` are robust of size three. Their repeats are respectively
`{0,2,4}` and `{1,3,4}`. The pole-intersection rule forces both `A_4`
copies to repeat `3`, and all three `B_4` copies to repeat `0`.

Build an adjacent target of class `A_4` with repeated colour `0`:

| Target corner | Source |
| --- | --- |
| bichromatic `(0,0,1)` | the repeat-`0` copy of `A_3` |
| bichromatic `(0,0,4)` | one `B_4` copy |
| `1 -> 0` | another `A_3` copy |
| `1 -> 2`, `4 -> 0`, `4 -> 2` | the three `B_0` copies |
| `1 -> 3`, `4 -> 3` | the two `A_4` copies |

This uses eight distinct adjacent cubes; none of the three opposite
cubes is needed in the final construction. Every possible case has
therefore yielded a solution.

## Scope

This is a hand proof for the reverse six-class branch of the
three-identical-opposite-cube analysis. It does not by itself cover
all three-opposite-cube failures; the other normal-form branch is the
butterfly family treated separately by the parent investigation.
