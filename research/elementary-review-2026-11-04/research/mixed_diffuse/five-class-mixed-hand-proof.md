# Five copies in one class, with diffuse opposite sources

**Status: elementary proof.** No enumeration is used below. The input
concentration bound is the previously proved six-class lemma: a failing
fourteen-pool has at most five copies in each adjacent tricolour class.

**Theorem.** A fourteen-pool containing five copies from an adjacent
tricolour class and at least one opposite-repeat source is soluble,
provided no opposite variety occurs more than twice.

Together with the separate pure-adjacent five-class theorem, this removes
every adjacent class of size five from the remaining diffuse branch.

## 1. Notation and two elementary bounds

Colours are 0,1,2,3,4, and `ab` denotes the directed tricoloured corner
a→b. Write C(S) for the cut S→Sᶜ. Its pole pair is its two-element side.
Its three varieties are indexed by the repeated colour outside that pair.
Thus four copies of a class contain a same-repeat pair, supplying both
bicoloured corners of a target of that class. Opposite varieties are
bidirected K₂,₂ graphs on four colours.

Normalize the distinguished class to A=C(01). Its six corners form a
two-by-three array with rows 0,1 and columns 2,3,4. The adjacent classes
disjoint from A are precisely

    B=C(234), Z23=C(23), Z24=C(24), Z34=C(34).

The reverse of A has three two-corner columns q→{0,1}. A B source sees
all three, and a Z source sees two entire columns. Every opposite source
meets A, and also its reverse, in either two corners in different columns
or four corners forming a two-column rectangle. Moreover a two-corner
intersection determines the opposite variety uniquely: its two undirected
edges determine the omitted colour and the bipartition.

We also use the shared-four bound: two adjacent classes with four common
corners have at most seven copies in a failure. Otherwise choose a class
with at least four copies, reserve a same-repeat pair for its bicoloured
corners and two further copies for its two private tricoloured corners,
and fill the four common corners from the other four sources.

## 2. Three useful eight-cube constructions

Call an adjacent source **disjoint** if it has no tricoloured corner of A.

### Construction I: four A, three disjoint sources, one opposite source

Choose two reverse-A columns met by the opposite source. On these four
positions, every disjoint source sees one whole column or both. If the
three disjoint sources do not all see just the same single column, the
four sources have a perfect matching: the three disjoint sources jointly
see all four positions, and any two of them together with the opposite
source see at least three.

In the exceptional case all three disjoint sources have the same class:
each sees the common column and the third column. Retarget to those two
columns. The three sources are now universal on the four reverse
positions, and the opposite source still sees at least one. In either
case the four A copies fill the four forward positions of the resulting
opposite target.

Consequently, if a failing pool contains at least four A and one opposite
source, it contains at most two sources disjoint from A.

### Construction II: three A, three disjoint sources, two opposite sources

Apply Construction I's reverse-half argument using the first opposite
source. The second opposite source meets the selected forward half,
because it meets at least two of the three A columns. It and three A
copies fill that half.

Consequently, if a failure contains at least three A and two opposite
sources, at most two adjacent sources are disjoint from A.

### Construction III: three A, four disjoint sources, one opposite source

The four disjoint sources match the reverse positions of some two-column
rectangle. If three of them miss the same column, select the other two;
otherwise every missing-column class occurs at most twice, and any two
columns work. This is Hall's theorem for two position pairs: at most two
sources are confined to either pair. The opposite source and three A
copies fill the forward half.

Consequently, if a failure contains at least three A and one opposite
source, at most three adjacent sources are disjoint from A.

## 3. Five A and two distinct opposite varieties

First we record a stronger two-disjoint-source construction:

> Four A, two disjoint adjacent sources, and two distinct opposite
> varieties always assemble an opposite target.

Here is an elementary three-column matching argument. Write P,Q for the
reverse-A intersections of the opposite sources. Each meets at least two
columns, and |P∪Q|≥3. Write Z,W for the two disjoint sources' reverse-A
intersections; each contains at least two complete columns.

If Z,W have two whole columns in common, select them. Both are universal
on the selected rectangle. If P,Q can fill two different positions there,
we are done. Otherwise both restrict to the same singleton. Each also
meets the third column, and their union on that column has at least two
positions. Retarget to the third column and the singleton's column:
P,Q fill the third column, and Z,W fill the other column.

The remaining case has Z and W missing distinct columns x,y. On the
rectangle x,y, they fill one position in each column, while P,Q fill the
other positions provided P and Q can be assigned different columns.
If this fails, both P,Q miss the same one of x,y, say y. They therefore
both meet x and the third column z. Retarget to x,z. The source W is
universal, while P,Q and Z match three positions: each has at least two
positions there, and their union has at least three. This completes the
reverse half; four A fill the forward half.

Replacing one A in this construction by a third opposite source gives
another useful eight-cube core: three A, two disjoint sources, and three
opposite sources with maximum variety multiplicity two always solve.
Indeed choose two distinct opposite varieties for the reverse-half
construction; the remaining opposite meets the selected forward half
and completes it with three A.

Consequently a failure with at least four A and two distinct opposite
varieties has at most one disjoint adjacent source. A failure with at
least three A and at least three diffuse opposite sources also has at
most one disjoint adjacent source.

We can now show that nine pieces suffice for the five-copy assertion:
five A, two distinct opposite varieties, and two arbitrary additional
sources.

Reserve a same-repeat A pair for the bicoloured positions of an A target.
If either of the two additional sources meets A, it and the two opposite
sources match three A corners. Each opposite sees at least two corners,
and their union has at least three, since a two-corner pattern uniquely
determines an opposite variety. Hall therefore gives the three-corner
matching; the three remaining A fill the other corners.

Otherwise both additional sources are adjacent and disjoint from A.
The stronger construction just proved solves using four A, those two
sources and the two opposite varieties.

We may therefore assume that the fourteen-pool contains just one opposite
variety O, with multiplicity t=1 or2.

## 4. A two-corner Hall cover

Let z count adjacent sources disjoint from A. Construction I gives z≤2.
After a same-repeat A pair is reserved for its bicoloured corners, three
A remain. Therefore the nine outside sources cannot match three A
corners in a failure.

By König's theorem their incidence graph has a vertex cover of size at
most two. Two source vertices cannot cover it, because at least seven
outside sources meet A. A source vertex and a corner vertex cannot
cover it either. For t=2, one opposite copy remains uncovered and sees
at least two corners. For t=1, the exceptional source must be O; all
eight other outside sources are then either disjoint or in the unique
adjacent class meeting A in that single corner. Since z≤2, that class
would contain at least six copies.

Hence all outside intersections are contained in two A corners H. The
intersection O∩A is exactly H. It is a pair in different columns, so up
to symmetry there are only two forms: a row pair or a diagonal pair.

## 5. Row pair: H={13,14}

Here O has corners ±{13,14,23,24}. The allowed outside adjacent classes
and their counts are

| Class | Symbol | Count | Intersection with A |
|---|---|---:|---|
| C(234) | B | b | empty |
| C(124) | D | d | 13 |
| C(123) | E | e | 14 |
| C(12) | F | f | 13,14 |
| C(23) | Z23 | c | empty |
| C(24) | Z24 | g | empty |
| C(34) | Z34 | h | empty |

Their total is 9−t. Each count is at most five, and the shared-four bound
gives d+f≤7 and e+f≤7. Write z=b+c+g+h.

The reverse-A position pools are as follows:

| Position | Adjacent classes containing it | O contains it? |
|---|---|---|
| 20 | B,D,E,F,Z23,Z24 | no |
| 21 | B,Z23,Z24 | no |
| 30 | B,E,Z23,Z34 | no |
| 31 | B,Z23,Z34 | yes |
| 40 | B,D,Z24,Z34 | no |
| 41 | B,Z24,Z34 | yes |

Four A can supply the forward positions of any rectangle target with
parts {0,1} and two of {2,3,4}.

### 5.1. Two O copies

Use the two O at31,41 in the rectangle on columns3,4. Positions30 and40
have at least two adjacent neighbours in their union, since their union
has size7−f≥2. Thus failure forces one position pool to be empty. By
interchanging3 and4, suppose b=e=c=h=0. Only D,F,Z24 remain, totalling7.

If g>0, use the rectangle on columns2,4:

    four A forward; O at41; Z24 at21;
    another D or Z24 at40; another D,F or Z24 at20.

This is possible since d+g=7−f≥2. Therefore g=0 and d+f=7. Both d,f
are at least two, and one is at least four.

If d≥4, reserve a same-repeat D pair and fill a D target by

    D:40,43; F:10,20; A:13; O:23.

If f≥4, reserve a same-repeat F pair and fill an F target by

    F:10,20; A:13,14; D:23; O:24.

Both constructions are possible, a contradiction.

### 5.2. One O copy

There are eight outside adjacent sources. Consider the rectangle on
columns3,4. Hall's theorem on its reverse positions30,31,40,41 says
that it solves unless at least one of the following holds:

    b+e+c+h=0;  b+d+g+h=0;  z=0;  d+f=7;  e+f=7.

For completeness: the first two alternatives are empty singleton pools;
the pair31,41 has only z+1 neighbours; the triples30,31,41 and31,40,41
have respectively9−d−f and9−e−f neighbours. All other Hall inequalities
follow from f≤5, d+f≤7 and e+f≤7.

If b+e+c+h=0, only D,F,Z24 remain. Now d+f≤7 forces g≥1, and
d+g=8−f≥3, so the columns2,4 construction above works. The second
empty-pool alternative is symmetric.

If z=0, only D,E,F remain, with total8. The shared-four bounds force
d,e≥1, and at least one is at least two. Assume d≥2. Assemble the
opposite target with parts {0,3} and {2,4}:

    A:02,04; O:32; E:34; D:40,43;
    two further D,E,F sources:20,23.

Every source in the last pool fits20. A remaining D or F fits23: failure
of that assertion would mean d=2,f=0,e=6, contrary to the class bound.

Finally suppose d+f=7; the case e+f=7 is symmetric. There is one other
outside adjacent source. If it is B,Z23 orZ24, use it at21 in the
columns2,4 rectangle, with D at40, F at20 and O at41. If it is E, the
z=0 case just proved applies. If it is Z34, one of d,f is at least four,
and the corresponding same-repeat construction of Section5.1 works.

Thus the row-pair case is always soluble.

## 6. Diagonal pair: H={02,14}

Here O is the opposite target with parts {0,4} and {1,2}. The allowed
outside adjacent classes are

    B=C(234), D=C(123), E=C(034), Z23, Z24, Z34,

with counts b,d,e,c,g,h, respectively. Their total is9−t, and again
z=b+c+g+h≤2. Every count is at most five.

In O itself, A supplies02,14. The remaining positions split into the
private triples

    L={10,20,24}, supplied by D;
    R={01,41,42}, supplied by E.

The disjoint sources B,Z24 meet L at20 and R at41; Z23 meets L at20,24;
Z34 meets R at41,42. The permutation (0 1)(2 4) interchanges D and E,
Z23 and Z34, and preserves A and O.

### 6.1. Two O copies

If z≤1 then d+e≥6. Since neither exceeds five,
min(d,3)+min(e,3)≥4. Use two A at02,14, four D/E sources in their
private triples, and the two O at the remaining two positions.

If z=2, try the rectangle on columns2,4, using four A forward and
the two O at20,41. The two disjoint sources can fill21,40 unless both
are Z23 or both are Z34. By symmetry take both to be Z34. If e>0,
assemble the rectangle on columns3,4 with

    four A forward; Z34:30,40; E:31; O:41.

If e=0, then d>0, and instead use Z34 at31,40, D at30 and O at41.

### 6.2. One O copy

Now d+e≥6. If d,e≥2, then min(d,3)+min(e,3)≥5. Use two A at02,14,
five D/E in their private triples, and O at the remaining position.

Otherwise symmetry gives d=1,e=5,z=2. If a disjoint source is B,Z23
orZ24, use

    A:02,14; E:01,41,42; D:10; disjoint source:20; O:24.

If both disjoint sources are Z34, use the columns3,4 construction of
Section6.1 with Z34 at30,40, E at31 and O at41.

This closes the diagonal case and proves the theorem.

## 7. A thirteen-cube corollary of the constructions

Sections 5 and 6 use at most four A copies in every assembly. Therefore
they also prove the following more local statement, without an initial
five-copy A class:

> Take four A, t copies of a single opposite variety O (t=1 or2), and
> 9−t adjacent sources, every one of whose A intersections is contained
> in the two-corner set O∩A. Suppose adjacent class counts are at most
> five and the shared-four bound holds. Then these thirteen cubes solve.

Construction I still supplies the required bound z≤2 on sources
disjoint from A. This corollary is useful when a Hall cover has one
exceptional source, which can simply be discarded.

## 8. What remains

This theorem does not classify all diffuse fourteen-pools. It reduces a
putative mixed diffuse failure to adjacent class counts at most four.
The three constructions give additional necessary conditions: a class
of size four has disjoint-adjacent mass at most two; a class of size
three has disjoint mass at most two when there are at least two opposite
sources, and at most three when there is just one.

The separate computer verification of the diffuse eight-cube lemma, if
used, further limits the total number of opposite sources to1,2,3 or4.
That last restriction has not been proved by the hand arguments here.
