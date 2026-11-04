# The missing path for two nonneighbouring opposite pairs

This is an elementary argument, independent of the inventory search.
It proves the missing-path reduction and closes two of the three
orientation families. The remaining alternating family is handled
by the companion pair-profile argument.

Normalize the four opposite sources to two copies each of

    P=O71={01,02,14,24},    Q=O73={01,03,12,23}.

An undirected edge denotes both directed corners. Their common edge
is01, and the complement of their union is the path0–4–3–1.
There are ten adjacent sources, each class occurring at most three
times. Set X=P\Q and Y=Q\P, as directed corner sets.

## 1. Two elementary completion rules

### Rank four on X or Y suffices

If four distinct adjacent cubes match four corners of X, put two Q
copies at01,10. The two P copies fill the two remaining positions of
X. This is an opposite assembly of P. The rule for Y is symmetric.

### Seeing both directions of a missing-path edge suffices

The three following targets each meet P and Q in a common bidirected
edge and one additional bidirected edge apiece:

| Missing edge f | Target | P intersection | Q intersection |
| --- | --- | --- | --- |
| 04 | O70={01,04,12,24} | 01,24 | 01,12 |
| 13 | O74={01,02,13,23} | 01,02 | 01,23 |
| 34 | O68={01,03,14,34} | 01,14 | 01,03 |

If the adjacent pool has a source for each direction of f, choose
two such sources. They are distinct because an adjacent cut contains
at most one direction of an edge. Assign them to the two f positions.

Write J for the other six target positions. The four opposite sources
can fill **any four positions of J**. The two corners private to P
have two P neighbours, those private to Q have two Q neighbours,
and any position set meeting both private groups or the common edge
has all four opposite neighbours. Hall's inequalities follow.

Every remaining adjacent source has a corner in J: its target
intersection uses at least two different underlying edges. At most
two adjacent classes can have their entire J-intersection confined
to a fixed single corner c. Such a source must have a two-corner
target intersection consisting of c and one direction of f. The
other two target edges do not cross its cut, so their endpoint
identifications, together with the direction of c, determine the
direction on f uniquely. Only the placement of the fifth colour
remains, giving at most two classes.

Consequently at most six adjacent sources can be confined to one
fixed corner of J. Eight adjacent sources remain. Their possible
corners therefore include two different positions, and two distinct
remaining sources can be chosen for those positions. The four
opposite sources fill the remaining four positions of J.

This proves the rule without using or reflecting any physical cube.
All eight selected sources are distinct.

## 2. Three orientation families

In an opposite-target failure, at least one direction of each edge
of0–4–3–1 must therefore be absent from the entire adjacent pool.
Choose one absent direction on each edge. Reversal of all corners
and reversal of the path reduce the choices to three patterns:

| Pattern along0–4–3–1 | Absent corners | Allowed adjacent outsets S |
| --- | --- | --- |
| +++ | 04,43,31 | 134;123;12;13 |
| ++− | 04,43,13 | 234;134;123;034;13;23;34 |
| +−+ | 04,34,31 | 134;124;04;12;024;14;014;24 |

Here the class is C(S)=S→Sᶜ and |S| is two or three. The table can
be read directly as a list of balanced upper sets: absence of u→v
means that including u in S forces v into S. The fifth colour2 is
isolated from these three implications.

The corresponding root-model class lists are, respectively,

    [3,7,8,10],
    [1,3,7,9,10,14,18],
    [3,5,6,8,11,12,15,16].

## 3. The monotone family +++

Write the counts of classes3,7,8,10 as a,b,c,d. Since each is at
most three and their sum is ten, all four are positive and b+c≥4.

Class3 has corner42 in X. Both classes7 and8 have all three corners
14,20,24 in X. Use one class3 cube at42 and three distinct cubes
from classes7 and8 at14,20,24. Thus the adjacent matching rank on X
is at least four, and the first completion rule applies.

## 4. The one-change family ++−

Use counts a,b,c,d,e,f,h for classes1,3,7,9,10,14,18. Their
intersections with X and Y are:

| Count | Class | X corners | Y corners |
| --- | --- | --- | --- |
| a | C234 | 20,41 | 21,30 |
| b | C134 | 42 | 12,30,32 |
| c | C123 | 14,20,24 | 30 |
| d | C034 | 02,41,42 | 32 |
| e | C13 | 14 | 12,30,32 |
| f | C23 | 20,24 | 21,30 |
| h | C34 | 41,42 | 30,32 |

Set α=a+f and β=b+e. These sources match all four available Y
corners12,21,30,32 precisely when

    α≥1,    β≥1,    β+d+h≥2.

To verify sufficiency by Hall, corner12 has β neighbours and21 has
α. The set{12,32} has β+d+h neighbours. The pair{12,21} has
α+β≥2. Every other nontrivial Hall inequality is immediate from
ten sources and the cap three: corner30 and every remaining pair
or triple see at least ten minus one class, hence at least seven
sources. The full four-corner set sees all ten. Necessity follows
from the same corner and pair counts.

If these conditions hold, the rank-four completion rule on Y solves
the pool. Otherwise there are three cases.

### Case α=0

Here a=f=0. If c,d>0, assign one c source to20 and one d source
to02. Every remaining adjacent source sees one of14,24,41,42.
Only class b is confined to42 and only class e is confined to14;
the other present classes have at least two of these corners.
At most three of the eight remaining sources can be confined to a
single position. Two more sources therefore fill two distinct
positions, giving rank four on X.

If c=0, the four classes b,d,e,h must all be present, since any
three have capacity at most nine. Match

    d:02,    e:14,    h:41,    b:42.

If d=0, similarly b,c,e,h are all present. Match

    c:20,    e:14,    h:41,    b:42.

The case c=d=0 is impossible by total capacity. This closes α=0.

### Case β=0

Here b=e=0. If c,d>0, assign c to14 and d to02. Every remaining
source then has at least two corners among20,24,41,42, so any two
additional sources can fill two distinct positions.

If c=0, the four classes a,d,f,h are present. Match

    a:20,    f:24,    d:02,    h:41.

If d=0, the four classes a,c,f,h are present. Match

    a:41,    c:14,    f:24,    h:42.

Again rank four on X follows.

### Case α,β>0 but β+d+h<2

Integrality gives β=1 and d=h=0. The total is

    a+f+c+1=10.

The cap three forces a=f=c=3. Use two different a sources, one f
source, and one c source as follows:

    a:41,    f:24,    c:14,    another a:20.

This also has rank four on X.

Every one-change configuration therefore assembles an opposite target.

## Status

The missing-path reduction and the two closures above are complete
hand arguments. They leave only the alternating family from Section2.
The companion pair-profile proof reduces that family to four
3,3,3,1 patterns and closes them using two own-looped triples with
intersecting pole pairs.
