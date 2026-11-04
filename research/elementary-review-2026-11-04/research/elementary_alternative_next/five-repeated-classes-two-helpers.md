# Five repeated adjacent classes and two further classes

4 November 2026

**Status: elementary proof; independent root audit passed.**

## Theorem

Take adjacent-repeat sources from seven different tricoloured-corner
classes, with multiplicities

    3,2,2,2,2,1,1.

These thirteen sources contain an eight-source five-colour assembly.
In particular a pure fourteen-cube failure cannot have exactly one
triple class.

The proof classifies five fixed doubled classes by a small geometric
Hall table, then gives explicit helper constructions. It does not
enumerate source inventories or repeated-colour refinements.

Throughout C(S) means the directed cut S→Sᶜ. A label such as01
denotes its outset, and a target written ab/cd has all eight directed
corners between the pairs ab andcd. Its two four-corner halves are
ab→cd andcd→ab. All sources may be properly rotated independently.

## 1. The Hall criterion for five doubled classes

Take two sources from each of five distinct adjacent classes, and
fix an opposite target T that their union supports. These ten sources
match T if and only if no three target corners are private to one
of the five classes.

Necessity is immediate: two source copies cannot fill three corners
available only in their class. For sufficiency, an adjacent cut meets
T in either two positions or one of its full four-position halves.
At most two classes can have their whole intersection in two given
positions. Therefore sets of six positions see at least three of
the five classes, hence six sources. Sets of seven or eight positions
see all five classes. Supported singletons and pairs have at least
two source neighbours. A three- or four-set can fail Hall only if
all its corners have neighbours in just one class, giving a private
triple.

Suppose a five-set S fails Hall. It then meets at most two classes.
Those two class intersections must cover all five positions because
T is supported. Two two-position intersections cannot do so. If both
intersections have size four, they must be opposite target halves:
equal halves would cover only four positions. They are disjoint, so
one class supplies at least three private positions of S. If one
intersection has size four and the other size two, at least three
positions of S are outside the latter intersection and are private
to the former. Thus every Hall failure again gives a private triple.
This proves the criterion.

## 2. Classifying the five doubled classes

If their tricoloured union supports no opposite target, the elementary
support-poset theorem puts them inside a common-corner family or a
butterfly family. See Section0 of
`../support_families/elementary-support-family-proofs.md`; the theorem
there concerns arbitrary cut collections, not just a fixed source
count. Five distinct classes in a butterfly are, up to its symmetries,
one of the two sets

    F1={01,02,124,123,12},
    F2={01,02,124,12,012}.                            (F)

These omit a low class or a high class from the six-class butterfly.
Its four high classes are interchanged by the permutations1↔2,
3↔4, and(1 3)(2 4) followed by reversal of all cuts. The last
operation also exchanges its two low classes. This verifies the
two possible omissions directly.
The common-corner alternative will be handled directly in Section3.

Now suppose a target is supported but none assembles. By Section1
some class has three private target positions. An adjacent cut meeting
an opposite target in at least three positions contains an entire
four-position directed half, since its only possible intersection
sizes and shapes are two positions or a full half. Its private triple
therefore consists of three positions in that half. Normalize this
class to A=C(01) and those positions to

    03,04,13.

The other four classes must avoid those three corners. The implications
0∈S⇒3,4∈S and1∈S⇒3∈S give exactly these eight possible outsets:

    U={234,134,123,034},     V={13,23,24,34}.

If three of the four classes belong to U, or three belong to V,
two copies each of those three classes and A already assemble.
The direct constructions are Section2 of
`../root/six-doubled-classes-hand.md`; they use only those eight
sources. Thus exactly two classes lie in each of U,V.

The following table treats all six choices from U against all six
choices from V. An ordinary entry is an opposite target supported
by the five classes and having no three positions private to one
class. Section1 therefore gives an assembly. Each entry is checked
by intersecting the five directed cuts with its eight positions.
The exceptional entries I,II,III are identified immediately below.

| U pair / V pair | 13,23 | 13,24 | 13,34 | 23,24 | 23,34 | 24,34 |
| --- | --- | --- | --- | --- | --- | --- |
| 234,134 | 01/24 | 13/24 | 01/24 | 12/34 | I | I |
| 234,123 | 01/24 | 13/24 | 01/24 | I | I | 12/34 |
| 234,034 | 01/24 | 13/24 | 01/24 | 12/34 | I | I |
| 134,123 | III | 02/34 | III | 12/34 | 01/24 | 12/34 |
| 134,034 | 01/24 | 03/14 | II | 12/34 | 01/24 | 01/24 |
| 123,034 | 01/23 | 12/34 | 04/12 | 12/34 | 01/24 | 12/34 |

The three exceptional representatives are

    I   ={01,234,02,014,012},
    II  ={01,02,124,024,24},
    III ={01,02,124,023,012}.                         (E)

Here are explicit relabellings for all nine exceptional cells,
so their identification requires no orbit enumeration. The tuple
lists the new labels of0,1,2,3,4. A final reversal reverses every
directed cut simultaneously.

| U pair | V pair | Representative | Relabelling tuple | Reverse cuts? |
| --- | --- | --- | --- | --- |
| 234,134 | 23,34 | I | (0,1,2,3,4) | yes |
| 234,134 | 24,34 | I | (0,1,2,4,3) | yes |
| 234,123 | 23,24 | I | (0,1,3,4,2) | yes |
| 234,123 | 23,34 | I | (0,1,4,3,2) | yes |
| 234,034 | 23,34 | I | (1,0,2,3,4) | yes |
| 234,034 | 24,34 | I | (1,0,2,4,3) | yes |
| 134,123 | 13,23 | III | (0,3,1,4,2) | yes |
| 134,123 | 13,34 | III | (0,3,2,4,1) | yes |
| 134,034 | 13,34 | II | (1,0,3,2,4) | no |

This proves the required classification: unless the ten doubled
sources already assemble, the five classes either have one common
corner, form one of(F), or form one of(E).

## 3. The common-corner case

One of the five repeated classes has a third actual source. The
five classes therefore have counts3,2,2,2,2 through a common corner.
They contain a3,2,2,2,1 subpool, which assembles by
`../pure_supported/common-corner-32221-hand.md`.

The two singleton helpers are unnecessary in this case. This is
the only point of the proof that uses the third source in a
repeated class.

## 4. The butterfly case F1

The four high classes01,02,124,123 are all doubled. Their union
with the two low classes12,012 misses precisely31,32,41,42.
Any class outside the six-class butterfly contains at least one
of these four corners. At most one of the two distinct helper
classes is the remaining low class012, so an outside helper exists.

If it has31, target03/14 is assembled by

    helper:31; C01:04,13; C02:01;
    C124:40,43; C123:10,34.

Interchanging1,2 and interchanging3,4 preserve the doubled high
classes and act transitively on31,32,41,42. Thus any outside helper
works. This is also the explicit butterfly construction in the
six-doubled-classes note.

## 5. The butterfly case F2

Write A=C01,P=C02,L=C124,Q=C12,H=C012, all doubled.

If a helper has41, use target01/24:

    helper:41; A:02,12; P:04,21; Q:20,14; L:40.

If a helper has42, use target02/14:

    helper:42; A:04,12; P:01,21; Q:10,24; L:40.

Otherwise both helpers avoid41,42. Outside the five core classes,
the only allowed helper classes are

    C03,C123,C13,C023,C23,C013.

Every one contains34; all except C123 contain31 or32. Since the
helpers have distinct classes, one can supply31 or32 and the other
can supply34. If the first supplies32, use target03/24:

    helpers:32,34; A:02,04; Q:20,23; L:40,43.

If it supplies31, use target03/14:

    helpers:31,34; P:01,04; Q:10,13; L:40,43.

This closes F2 using only two copies of every core class.

## 6. Exceptional type I

Write A=C01,B=C234,P=C02,D=C014,H=C012, all doubled.

A helper at32 gives target12/34:

    helper:32; A:13,14; B:31,41; P:23,24; D:42.

A helper at any corner c in {20,40,41} gives target01/24:

    helper:c; B:the other two corners of{20,40,41};
    P:04,21; D:02,12; H:14.

The only helper class outside the core avoiding both32 and all of
20,40,41 is C023. Two distinct helper classes cannot both be this
class, so one of the displayed constructions applies.

## 7. Exceptional type II

Write A=C01,P=C02,L=C124,R=C024,Z=C24, all doubled.

A helper at any corner c in {02,12,14} gives target01/24:

    helper:c; A:the other two corners of{02,12,14};
    P:04,21; L:20,40; R:41.

If neither helper meets that set, their only possible classes
outside the core are

    C234,C023,C23,C34.

Every one contains31, and all except C023 contain30. Distinct
helpers can therefore fill30,31 in target01/34. Its other six
positions are supplied by

    A:04,14; P:03; L:13,40; R:41.

This closes type II.

## 8. Exceptional type III

Write A=C01,P=C02,L=C124,R=C023,H=C012, all doubled.

A helper at any corner c in {10,40,43} gives target03/14:

    helper:c; L:the other two corners of{10,40,43};
    R:31,34; P:01,04; A:13.

If neither helper meets that set, their only possible classes
outside the core are

    C03,C034,C23,C013.

All except C23 contain32, so one of two distinct helpers contains
32. Use target03/12:

    helper:32; A:02,13; P:01,23; L:10,20; R:31.

Thus type III also assembles. All cases of the core classification
are now closed, proving the theorem.

## 9. Consequence for a pure fourteen-pool with one triple

In a hypothetical pure fourteen-failure, at most eight classes are
occupied and at most five have multiplicity at least two. Every
class has multiplicity at most three. If precisely one is a triple,
let d be the number of doubled classes and s the number of singletons.
Then

    3+2d+s=14,   1+d+s≤8,   1+d≤5.

These inequalities force d=4,s=3. Retain the triple, the four
doubled classes and two of the three singleton classes. The
thirteen-source theorem above gives an assembly, a contradiction.

Therefore every pure fourteen-failure has at least two triple
classes. This deduction uses the existing pure concentration,
diversity and six-repeated-class bounds; none depends on the
one-opposite fifteen-cube theorem.

## Verification scope

The6×6 table is a table of five cut geometries and opposite target
incidences. Its completeness follows from the private-triple Hall
criterion and the explicit eight-class avoidance list. The helper
proofs display every source assignment and the small cut lists they
use. No list of thirteen- or fourteen-cube inventories is assumed.
