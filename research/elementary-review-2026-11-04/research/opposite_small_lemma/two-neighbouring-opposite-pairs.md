# Two neighbouring opposite pairs and two further opposite sources

**Proved elementary lemma.** Let A,B be distinct opposite varieties
sharing four directed corners, equivalently two undirected edges.
Take two copies of each. Add two opposite sources C,D, neither of
which is A or B (they may equal each other), and any two further
five-colour cubes. These eight sources have an opposite-target assembly.

The proof uses the three-opposite-pairs lemma in the companion note.
There is no multiplicity restriction on the two arbitrary sources.

## 1. The line of three four-cycles

Use undirected four-cycle notation, with each edge denoting both
directed corners. Put

    I=A∩B, J=A\B, K=B\A, T=A symmetric-difference B=J∪K.

Each of I,J,K has two edges, and T is a four-cycle. The three cycles
A=I∪J, B=I∪K, T=J∪K form a line: their union is either K4 (when
I consists of disjoint edges) or K2,3 (when I consists of adjacent edges).
Each union edge occurs in exactly two of the three cycles.

Every opposite variety E outside {A,B,T} has two edges in this union.
For a K4 union this follows because E uses the fifth vertex, leaving
only a two-edge path on the other three vertices. For a K2,3 union,
the number of crossing edges in the four-cycle E is even; it cannot
be zero, and if it were four E would be one of A,B,T. Thus it is two.

Since E meets each of A,B,T in at least one edge, its intersection
sizes with the three are therefore (2,1,1) in some order. Call the
cycle with intersection size two its high target. More precisely,

* high A: one edge of I and one of J;
* high B: one edge of I and one of K;
* high T: one edge of J and one of K.

## 2. A robust-six criterion

Six opposite sources, with every variety occurring at most twice, can
fill any six corners of a target E if:

* each source intersects E in at least two undirected edges;
* each edge of E is present in at least two source copies.

For Hall's theorem, one edge pair has at least two neighbours. A set
meeting two target edges has at least four: only one opposite variety
can have its E-intersection confined to the complementary two edges,
and that variety has at most two copies. A set meeting at least three
target edges sees all six sources. Thus every set of at most six
positions has enough neighbours.

If C or D equals T, or if C,D have the same high target, this criterion
immediately supplies the needed robust-six target. At A or B the two
copies of that variety provide the edge-frequency bound; at T the
two A and two B copies provide it because J and K partition T.
The arbitrary additional sources can then fill any two distinct
compatible corners.

It remains that C,D have different high targets.

## 3. Two elementary six-corner completion rules

The following rules are useful on target A=I∪J. Its source pattern
consists of two universal A copies, two B copies seeing I, one C
copy seeing one edge of I and one edge of J, and one other source D.

**Rule I.** If D sees one edge of I, the six sources can fill every
six-position set whose two omitted corners are not both in I.

If one omitted corner is in I and one in J, the remaining three J
corners are filled by C and the two A copies: C's two J corners
cannot both be omitted. The three remaining I corners are filled
by D and the two B copies. If both omitted corners are in J, the
two A copies fill the two remaining J positions. C,D can be assigned
distinct I corners (each has two), and the two B copies fill the rest.

**Rule II.** If D sees the single edge e in J, the six sources can
fill every six-position set unless the omitted pair consists of
both directions of e.

Assign D an available e corner. If three J positions remain, neither
omitted corner was in J; C still has a J corner and it joins the
two A copies there. The two B copies fill the two remaining I
positions. If two J positions remain, use the two A there, and
C plus two B at the three remaining I positions. If one J position
remains, use one A there and the other A, C and two B at the four
I positions. Every stated assignment has a compatible corner.

## 4. Different high targets

First suppose C has high target A and D high target B. On target A,
D sees one edge of I, so Rule I applies. On target B the symmetric
Rule I applies. Every additional cube has a corner of the opposite
target T=J∪K. If that corner is in J, reserve it as a hole in A;
if it is in K, reserve it as a hole in B. The other additional cube
has at least two corners of the selected target and hence can fill
a different position. The omitted pair is not confined to I, so
the corresponding six-corner completion works.

Next suppose C has high target A and D high target T. On target A,
D sees an edge e of J, so Rule II applies. It yields an assembly
unless both additional cubes have all their A-compatible corners
inside the bidirected edge e.

An adjacent cut cannot have this property: it has at least two
corners of A, on distinct undirected edges. Both additional sources
would therefore be opposite varieties whose intersection with A is
exactly e. There are precisely two such varieties; one is D, and
write R for the other. (They are obtained by omitting one or the
other of A's vertices not on e.)

If an additional source is D, the pool contains two copies each
of A,B,D. If neither is D, both are R, and it contains two copies
each of A,B,R. In either case the three-opposite-pairs lemma applies.

The case of high targets B and T is symmetric. These exhaust the
possibilities, proving the lemma.

## Consequence for the diffuse fourteen-cube problem

If a pool has at least six opposite sources, every opposite variety
occurs at most twice, and two doubled varieties share four corners,
it is soluble. Choose those four sources, any two other opposite
sources, and any two further sources.

Combining this with the three-opposite-pairs lemma, a still-failing
pool with at least six opposite sources could have at most two
doubled opposite varieties; if it has two, they must share only
two corners. The cases with two such nonneighbouring doubled types,
one doubled type, or no doubled type are not settled by this note.

