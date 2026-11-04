# The alternating-path family for two nonneighbouring opposite pairs

**Theorem.** Let

    P=O71={01,02,14,24}, Q=O73={01,03,12,23},

where an undirected edge denotes both directed corner positions.
Take two copies of each. Add ten adjacent sources, with class
multiplicities at most three, whose classes avoid the three arcs

    04,34,31.

Then the pool assembles a five-colour target.

These three forbidden directions alternate along the path0–4–3–1.
The proof classifies the remaining multiplicities by two four-corner
Hall tests, then closes the only residual using repeated colours.

## 1. Eight allowed classes and two useful targets

Write C(S)=S→Sᶜ. The allowed classes and their counts are

| Count | Class | Model class index |
|---|---|---:|
| a | C(134) | 3 |
| b | C(124) | 5 |
| c | C(04) | 6 |
| d | C(12) | 8 |
| e | C(024) | 11 |
| f | C(14) | 12 |
| g | C(014) | 15 |
| h | C(24) | 16 |

To derive this list, let s_v record whether colour v is in the
outset. Avoiding the three arcs says

    s_0≤s_4, s_3≤s_4, s_3≤s_1,

and the outset has size two or three. These inequalities give exactly
the eight displayed outsets, by choosing the values of s_3,s_4 and
then s_0,s_1,s_2. Thus the family is a direct cut classification,
not an inventory search.

Every count lies between zero and three, and

    a+b+c+d+e+f+g+h=10.

The common edge of P,Q is01. Put

    X=P\Q={02,20,14,41,24,42},
    Y=Q\P={03,30,12,21,23,32}.

If four adjacent sources match four corners of X, the two Q copies
fill01,10 and the two P copies fill the remaining two X corners.
Thus matching rank at least four on X gives target P. Likewise rank
at least four on Y gives target Q.

The adjacent intersections are:

| Count | X intersection | Y intersection |
|---|---|---|
| a | 42 | 12,30,32 |
| b | 20 | 23 |
| c | 02,41,42 | 03 |
| d | 14,20,24 | 23 |
| e | 41 | 03,21,23 |
| f | 42 | 12 |
| g | 02,42 | 03,12 |
| h | 20,41 | 21,23 |

There is a symmetry interchanging P,Q and the counts

    a↔d, b↔f, c↔e, g↔h.

It permutes colours by(0 1)(3 4) and reverses every directed corner.
Both opposite varieties remain compatible under direction reversal.

## 2. The outer counts a,d are at most one

Suppose d≥2. Assign two d sources to14,24. Every one of the remaining
eight adjacent sources meets

    Z={02,20,41,42}.

They cannot all be confined to one corner. At42 the only confined
classes are a,f, whose combined capacity is six. At20 the confined
classes are b and any remaining d, with combined count at most four.
At41 only e is confined, and no class is confined to02. Thus two
remaining sources match different Z corners, giving four matches in
X and hence target P.

By symmetry, a≥2 gives target Q. In a failure we therefore have

    a,d≤1.

Suppose d=1. Use that source at14. If the remaining nine sources
match three corners of Z, target P again assembles. Otherwise their
rank on Z is at most two. König's theorem supplies a cover by at most
two corner/source vertices. A one-corner cover would need at least
eight sources confined to that corner, whereas at most six are.
A cover containing no corners is also impossible. Hence all nine
source patterns lie in a pair of Z corners.

The six possible pairs have these eligible classes:

| Corner pair | Eligible count labels |
|---|---|
| 02,20 | b |
| 02,41 | e |
| 02,42 | a,f,g |
| 20,41 | b,e,h |
| 20,42 | a,b,f |
| 41,42 | a,e,f |

The total of nine and cap three force three classes to occur three
times each. The three possibilities containing a contradict a≤1.
Thus the only unresolved case with d=1 is

    d=1, b=e=h=3,

with all other counts zero. Symmetrically, the only unresolved case
with a=1 is

    a=1, c=f=g=3.

## 3. The case a=d=0

Set

    L=c+f+g, R=b+e+h,

so L+R=10 and 1≤L,R≤9. All X corners available to adjacent sources
now belong to Z={02,20,41,42}.

Hall's theorem says that all four Z corners can be matched exactly
when

    c+g>0, b+h>0, L≥2.                         (X)

Here c+g and b+h are the neighbour counts of02 and20. The neighbour
count of41 is c+e+h≥1, since the complementary counts b,f,g sum to
at most nine; the neighbour count of42 is L≥1. The pair{02,42} has
neighbour count L and gives the only nonautomatic two-position
inequality. Every other pair has at least four neighbours, since
its complement accounts for at most two classes of capacity three.
Every triple has at least seven neighbours. These observations prove
the asserted equivalence.

By the same calculation, target Q assembles exactly when the four
available Y corners can be matched, which holds if

    f+g>0, e+h>0, R≥2.                         (Y)

If L=1, then b=e=h=3. Conditions(Y) fail only if f=g=0, leaving

    c=1, b=e=h=3.

If R=1, the symmetric residual is

    e=1, c=f=g=3.

Suppose L,R≥2. To fail both tests, one of c+g=0 or b+h=0 must hold,
and one of f+g=0 or e+h=0 must hold. Pairing these alternatives gives
either L=0, R=0, or a pool supported on only two classes. The first
two contradict L,R≥2; the last has at most six sources rather than
ten. Thus there is no further case.

Consequently the only pools not already solved by target P or Q have
one of the four profiles

    c=f=g=3 with a=1 or e=1;
    b=e=h=3 with c=1 or d=1.

## 4. A thirteen-cube core closes every residual

It suffices to solve the core

    2P+2Q+3C(04)+3C(14)+3C(014),

since the other triple core is its image under the symmetry from
Section1. The singleton helper is unnecessary.

Call a class own-looped if, after reserving two of its cubes, the
remaining sources can match its six tricoloured corners. Both C(04)
and C(14) have such matchings:

| Target class | Matching of its six tricoloured corners |
|---|---|
| C(04) | P:41; Q:01,03; C(014):02,42; C(14):43 |
| C(14) | remaining C(14):40; Q:10,12; P:42; C(014):13; C(04):43 |

The first matching uses no C(04) source; the second uses only the one
C(14) source left after two have been reserved.

If two of the three C(04) cubes have the same repeated colour, reserve
them for the bicoloured positions and use the first matching to
assemble that adjacent target. Thus a failure would force the C(04)
repeated colours to be1,2,3. Similarly the C(14) repeated colours
would have to be0,2,3.

Choose their common repeated colour2. Reserve the C(04) cube repeating2
for the bicoloured corner(2,0), and the C(14) cube repeating2 for the
bicoloured corner(2,4). These are the bicoloured corners of the C(04)
target repeating2. Its six tricoloured corners are filled by the
first matching above: only one additional C(14) is needed, and two
remain available after the reservation. This is a full assembly,
contradicting failure.

Hence both triple cores assemble and every alternating-path case is
solved. The proof uses no exhaustive inventory classification.

**Smaller core.** The two own-loop matchings use only one P copy and
at most two C(014) copies. The same argument therefore proves the
stronger eleven-source statement

    P+2Q+3C(04)+3C(14)+2C(014) assembles.

No extra matching argument is required: every source used in the
displayed proof remains available in this smaller core.
