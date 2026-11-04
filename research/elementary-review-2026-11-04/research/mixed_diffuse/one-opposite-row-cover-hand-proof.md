# One opposite source: the row-triple Hall cover

**Status: elementary proof.** No enumeration of multiplicity vectors is
used below.

We use directed corners `ab`, adjacent cuts C(S)=S→Sᶜ, and opposite
varieties given by bidirected complete bipartite graphs on two pairs.
Suppose a putative fourteen-cube failure contains four A=C(01), one
O=opposite04|23, and nine adjacent helpers. Suppose every helper meets
A only in H={02,03,04}. Adjacent class counts are at most four, and
classes sharing four tricoloured corners have combined count at most
seven. Both bounds have already been proved for a failure.

Write Q={2,3,4}. The eligible helper classes are

    Fi=C(0i),  Gi=C({0}∪(Q\{i})),  Zi=C(Q\{i})  (i∈Q),
    B=C(Q).

The Zi and B are precisely the helpers disjoint from A. We will show
that this covered configuration always solves.

## 1. A disjoint helper gives an opposite assembly

For any helper X, let L(X) be the set of columns q for which X has
the reverse-A corner q1. Then

    L(Fi)={i};  L(Gi)=L(Zi)=Q\{i};  L(B)=Q.

Choose a disjoint helper Z. It has q0 and q1 for every q in a set
M of at least two columns. O has the reverse-A positions20,30, so
write P={2,3} for its columns. Let U be the union of the L sets of
the other eight helpers.

We have |U|≥2. For any two columns in U, two of these eight helpers
can fill their two q1 positions: otherwise at most one helper meets
either column, leaving at least seven helpers in the unique singleton
class Fi of the third column, contrary to the class bound four.

If distinct columns q∈M∩U and r∈P∩U can be chosen, assemble the
rectangle01|qr: Z supplies q0, O supplies r0, two other helpers supply
q1,r1, and four A supply the forward half.

The only way those distinct columns cannot be chosen is M=P={2,3}
and U={2,4} or {3,4}. Indeed all three of M,P,U have size at least
two in a three-element set; if both intersections are the same
singleton, M and P have the same missing column.

Thus Z=C(23), and by interchanging2 and3 we may take U={3,4}. The
other helpers are then F3,F4,G2 or C(34). If C(34) occurs, choose it
as Z instead: its column pair differs from P, and the preceding
rectangle construction works. Therefore the sole disjoint helper is
C(23), and the other eight helpers are F3,F4,G2.

Let their counts be x,y,z. Since F3,G2 and F4,G2 share four corners,
x+z≤7 and y+z≤7. Their total is eight, so x,y≥1. Assemble the
opposite target14|23, omitting0, by

    A:12,13;  C(23):21;  O:24,

and fill31,34,42,43 from F3,F4,G2. These helpers see respectively
{31,34}, {42,43}, {31,42}. Assign F3 to34 and F4 to43. The remaining
helpers match31,42: each position still has at least three neighbours,
because x+z=8−y≥4 and y+z=8−x≥4.

Consequently a failure in this row cover has no disjoint helpers.

## 2. The six-position path

Write a,b,c,d,e,f for the counts of F2,F3,F4,G2,G3,G4, respectively.
Their sum is nine, and each is at most four.

Consider the opposite target14|23. Two A supply12,13. Its remaining
six positions, in the order

    24,21,43,42,31,34,

have the following helper neighbourhoods:

* F2,G3,F4,G2,F3 are the five consecutive edges of this six-vertex path;
* G4 sees the outer four positions24,21,31,34;
* O sees the two ends and the two central positions24,43,42,34.

The four pairs of consecutive path-edge classes share four corners.
Thus their weight sums a+e, e+c, c+d, d+b are at most seven.

We now check Hall's theorem for these six positions.

* A set of five or six positions meets every helper, so is safe.
* A set of four positions can miss at most one path-edge class; it
  cannot miss G4. Hence it has at least9−4=5 helper neighbours.
* The complement of a three-position set contains at most two path
  edges. If it contains two, they are consecutive and have combined
  weight at most seven. G4 cannot be missed, and O must meet the
  chosen three positions. There are therefore at least9−7+1=3
  neighbours.

Only singleton and pair obstructions remain. The singleton positions
not already supplied by O are21 and31. Their failure conditions are

    a+e+f=0,              b+d+f=0.

For a pair, if O misses it then the pair is {21,31}, which has
9−c≥5 helper neighbours. Otherwise a deficient pair must have no
helper neighbour at all. For the central pair {43,42}, this means
c+d+e=0. For any other pair, G4 meets it, so f=0. Nine remaining
copies, each path-edge class of weight at most four, require at least
three positive path edges in the four-position complement. Those
three edges must form four consecutive vertices. The resulting
conditions are the two singleton conditions already listed, or
a+b+f=0.

Therefore failure of this opposite target forces one of

    a+e+f=0;   b+d+f=0;   c+d+e=0;   a+b+f=0.

The first three put all helpers in one of the families

    {F3,F4,G2},  {F2,F4,G3},  {F2,F3,G4}.

The fourth puts them in {F4,G2,G3}. This last family actually solves
another opposite target. Its counts c+d+e=9 obey c+d≤7,c+e≤7, so
d,e≥2. Assemble opposite12|34 by

    A:13,14;  O:24;  G3:23;  G2:31,32.

Two of the six remaining helpers fill41,42: every one sees41, and
at least c+d−2≥3 also see42.

Thus only the first three support families need to be considered.

## 3. The three support families

Interchanging2 and3 exchanges the first two families and preserves O.
It suffices to treat these two forms:

| Case | X | Y | Z |
|---|---|---|---|
| I | F3=C(03) | F4=C(04) | G2=C(034) |
| II | F2=C(02) | F3=C(03) | G4=C(023) |

Write x+y+z=9, with each count at most four.

Four copies of X or Y solve by reserving a same-repeat pair and using
the following six tricoloured positions. The two positions in the last
column are supplied by two sources from the other two classes; at least
five such sources are available.

| Case and target | Two remaining target-class copies | A | O | Two sources from the other classes |
|---|---|---|---|---|
| I, X | 31,32 | 04 | 34 | 01,02 |
| I, Y | 41,43 | 03 | 42 | 01,02 |
| II, X | 21,23 | 03 | 24 | 01,04 |
| II, Y | 31,32 | 02 | 34 | 01,04 |

Hence x,y≤3. If z=4, then x+y=5 and x,y≥2. Reserve a same-repeat Z
pair. In Case I use X at31,32, Y at41,42, A at02 and a remaining Z
at01. In Case II use X at21,24, Y at31,34, A at04 and a remaining
Z at01. Thus z=4 also solves. Necessarily x=y=z=3.

### Each class has a loop

The same Z-target construction works after reserving two of its three
copies. For X and Y, the following assignments work after reserving
their same-repeat pair:

| Case and target | Remaining target copy | Z | A | O | Two copies of the other class |
|---|---|---|---|---|---|
| I, X | 31 | 32 | 04 | 34 | Y:01,02 |
| I, Y | 43 | 41 | 03 | 42 | X:01,02 |
| II, X | 23 | 21 | 03 | 24 | Y:01,04 |
| II, Y | 32 | 31 | 02 | 34 | X:01,04 |

Thus all three copies of each class must have different repeated colours.

### The three classes conflict pairwise

If X and Y share a repeated colour, reserve one of each for an X
target's bicoloured positions. There are now two X copies left, so
the X row of the preceding four-copy table supplies the six tricoloured
positions. Two sources from Y,Z remain available for its common pair.

If X and Z share a repeated colour, they supply the bicoloured corners
of an A target: X has pole0, Z has pole1, and their common repeat lies
outside {0,1}. The same holds for Y and Z. In either case, one remaining
X and one remaining Y match two different A corners, and four A fill
the other four. Their A intersections are different two-element
subsets of {02,03,04}, so this two-matching always exists.

The three repeated-colour sets must therefore be pairwise disjoint.
Each has size three, requiring nine colours where only five exist.
This contradiction closes the row-triple cover.
