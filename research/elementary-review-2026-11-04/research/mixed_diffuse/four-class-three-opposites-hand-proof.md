# Four adjacent copies and three diffuse opposite sources

**Status: elementary proof.** This closes the g≥4, O=3 branch, without
the earlier computed three-helper lemma.

**Theorem.** A fourteen-pool containing at least four copies of an
adjacent tricolour class and exactly three opposite sources, with no
opposite variety occurring three times, is soluble.

Use the directed-corner notation of `five-class-mixed-hand-proof.md`.
The nine-piece lemma there handles any adjacent class of size at least
five, since the three opposite sources include two distinct varieties.
We may therefore suppose that every adjacent class has at most four
copies. Normalize the distinguished four-copy class to A=C(01).

We will use the following already proved eight-cube construction:

    3B + two adjacent sources disjoint from B + three diffuse O solve.

Thus any class of size at least three in a putative failure has at most
one adjacent source disjoint from it.

## 1. Reduction to three-corner covers

Reserve a same-repeat A pair for its bicoloured positions, leaving two
A. The three opposite sources have matching rank three on A: each sees
at least two corners, and three sources with only two corners between
them would be three copies of one opposite variety.

Suppose their union on A has at least four corners. A nonempty adjacent
source fails to extend them to a four-matching only if two of the
opposite sources are identical, have a two-corner A intersection P,
and the adjacent source's intersection is contained in P. This follows
directly from Hall: a deficient triple is the only possible obstruction,
since the four-source union already has size at least four.

There are seven other adjacent sources, and at most one is disjoint
from A. Consequently either an adjacent target solves at once, or all
seven adjacent sources have their A intersections in the same pair P.
The thirteen-cube corollary in the five-class note then solves using
four A, the two identical opposite sources and those seven adjacent
sources; the third opposite is unnecessary.

It remains that the three opposite sources' union on A is a set H of
size three. Any further source meeting A outside H extends their
three-matching and solves A. We may therefore assume all seven other
adjacent sources meet A only in H.

Up to the stabilizer of A there are three shapes for H, treated below.

## 2. A row triple: H={02,03,04}

The eligible opposite varieties are

    opposite02∣34, opposite03∣24, opposite04∣23,

all omitting colour1. Two distinct such varieties can match q0,r0 for
any two different columns q,r in {2,3,4}: their sets of available
columns are different two-element subsets of a three-element set.

Every eligible adjacent helper has at least one reverse-A position q1.
It has only one such position exactly when its class is C(0q); all
other eligible classes have at least two. Hence two helpers match q1,r1
for some distinct columns unless both are the same class C(0q).

The seven helpers cannot all belong to one class, since class counts
are at most four. Choose two with a matching to q1,r1, and choose two
distinct opposite sources at q0,r0. Four A fill0q,0r,1q,1r, completing
the rectangle target with parts {0,1} and {q,r}.

## 3. A column pair: H={02,03,12}

The opposite sources use both varieties

    T = opposite04∣23, omitting1;
    U = opposite02∣13, omitting4,

one twice and the other once. The three sources match20,21,30: use
T at20, U at21 and the repeated variety at30. Thus any helper at31
completes the rectangle01∣23 with four A.

The eligible helpers containing31 are C(234), C(034), C(23), C(34).
If none occurs, the remaining helper classes are

    D=C(134), R=C(04), S=C(024), Z=C(24).

If D occurs with any of R,S,Z, assemble the rectangle01∣24 using

    four A forward; T:20; U:21; D:40; R,S orZ:41.

Seven helpers cannot all be D, so D is absent in a failure. Likewise,
if Z occurs, some R or S occurs, and the same construction uses Z at40
and that other source at41. Thus Z is absent too.

The seven helpers are therefore R and S. One class has four copies,
and the other has three. If R has four, reserve a same-repeat R pair.
The remaining two R fill two of its six tricoloured positions; the
three opposite sources and one A match four more. Explicitly:

| Opposite counts | A | T copies | U copies |
|---|---|---|---|
| two T, one U | 02 | 42,43 | 01 |
| one T, two U | 02 | 42 | 01,03 |

If S has four, reserve a same-repeat S pair and use one R with the
three opposite sources for four tricoloured positions:

| Opposite counts | R | T copies | U copies |
|---|---|---|---|
| two T, one U | 01 | 03,43 | 21 |
| one T, two U | 01 | 43 | 21,23 |

The two remaining S fill the other two positions. This closes the
column-pair shape.

## 4. Three columns, split between the rows: H={02,03,14}

Write

    T = opposite04∣23, omitting1;
    U = opposite04∣13, omitting2;
    V = opposite04∣12, omitting3.

These are the eligible opposite varieties. Their reverse-A intersections
are respectively {20,30}, {30,41}, {20,41}. Thus any two distinct
opposite sources match any prescribed pair of positions from
P={20,30,41}.

Let K={21,31,40}. If two helpers match two K positions, select the
corresponding rectangle:21,31 uses columns2,3;21,40 uses2,4;31,40
uses3,4. Two distinct opposite sources fill its other two reverse
positions from P, and four A fill the forward half.

We may therefore suppose the helpers have matching rank at most one
on K. Their K intersections are:

| Helper class | K intersection |
|---|---|
| R=C(04) | empty |
| D=C(123) | empty |
| E=C(034) | 31 |
| F=C(024) | 21 |
| C(234), C(23), C(24), C(34) | at least two positions |

If one of the last four classes occurs, all six other helpers must be
R or D; any other nonempty K intersection would give a two-matching.
But R and D are reverse cuts and hence disjoint. Two counts totalling
six, each at most four, have one at least three and the other at least
two, contradicting the disjoint-source bound of the introduction.

Thus none of the last four classes occurs. Also E and F cannot both
occur. Interchanging2 and3 if necessary, assume F is absent. Write
r,d,e for the counts of R,D,E, with r+d+e=7.

Every eligible opposite source meets each of R and D in four corners.
Since A meets each of them, three opposite sources and one A match
four corners of either class. Four copies of R or D would therefore
solve after reserving a same-repeat pair. Hence r,d≤3.

Suppose e=4. Since D and E are disjoint, the disjoint-source bound gives
d≤1, so r≥2. In E the opposite intersections lie in

    M={01,02,41,42}:
    T sees02,42; U sees01,41; V sees all four.

The three opposite sources match three M positions, since no variety
occurs three times. An R source sees all M and fills the fourth. After
reserving a same-repeat E pair, the two other E fill31,32. Thus e=4
also solves, and e≤3.

The class D is disjoint from both R and E. If d=3, its disjoint mass
would be r+e=4. If d=2, then r+e=5 forces r or e to be three, and that
class has two disjoint D sources. Both violate the disjoint-source
bound. Therefore d≤1; since r+d+e=7 and r,e≤3, necessarily

    r=3, d=1, e=3.

This last form assembles V directly. Four of the six R/E sources fill
their common positions M. An A fills14. Of the three remaining target
positions {10,20,24}, two can be filled by opposite sources: T sees20,24,
U sees10, and V sees all three; failure to find a two-matching would
require three U copies. The D source fills the last position.

All three cover shapes are soluble. This proves the theorem.

## Consequence

Combining this theorem with `four-class-four-opposites-hand-proof.md`
shows, entirely elementarily, that a mixed fourteen-cube failure with
at least three opposite sources, each variety used at most twice, has
every adjacent class count at most three. The one- and two-opposite
four-class branches are treated in their respective companion notes.
