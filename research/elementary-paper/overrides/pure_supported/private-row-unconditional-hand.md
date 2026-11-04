# No triple in a failing pure fourteen-pool has a private row pair

**Lemma.** Consider a failing pool of fourteen adjacent-repeat cubes,
with every tricoloured class of multiplicity at most three. No triple
class has two private corners in one row of its two-by-three cut array.
Consequently every triple without an own-orientation loop has exactly
two private corners.

The dependencies are the nonprivate-triple lemma
`g3-nonprivate-hand.md`, the two-own-loop exclusion
`two-own-loop-triples-hand.md`, the six-repeated-class bound
`../root/six-doubled-classes-hand.md`, and the common-corner lemmas
cited below. None uses this row-pair exclusion.

## 1. Row geometry

Normalize the distinguished class to A=C(01), with private corners
02 and03, and put Q={2,3,4}. Every outsider avoids both private corners.
The possible outsider classes are exactly

    P_i=C(1i), N_i=C(1,Q\{i})  (i∈Q),
    H=C(023), B=C(234), Z_i=C(Q\{i})  (i∈Q).

The six P/N classes have the common corner 10. Write v for their total
multiplicity, h for the H multiplicity, and z for the total B/Z
multiplicity. Thus v+h+z=11, with every individual class count at most3.

In the reverse-A array, whose rows are q0,q1 for q∈Q, the P/N sources
meet only the 0-column:

    P_i sees i0;       N_i sees j0,k0.

Their intersections with A are complementary sets of columns in the
1-row: P_i sees 1j,1k, while N_i sees1i. A B/Z source sees both
positions in at least two reverse rows. H sees21,31 and no 0-column
position. Thus every source outside the P/N family that meets the
reverse 1-column meets at least two rows there.

### At most three zero-intersection sources

Suppose z≥4 and some nonzero-intersection outsider is present. If z≥5,
every reverse row sees at least z−3≥2 zero sources. Choose a two-row
rectangle containing a forward column met by a nonzero outsider X.
Four zero sources fill the reverse half: each row has degree at least2,
and every zero source meets their union. X and three A fill the forward
half.

If z=4, choose two reverse rows each having zero-source degree at least2.
At most one row can fail this bound. The seven nonzero outsiders cannot
all meet A in the remaining column: only the two singleton-intersection
classes for that column could do so, with total capacity6. Thus an X
meeting the chosen rectangle exists, and the same construction works.

If every outsider is zero, z=11. The three Z classes have capacity9,
so B is present; their combined count is at least8 because B≤3.
The Z sources alone match all six corners of reverse A: every row has
at least five neighbours and any two rows see all Z sources. A repeated
colour among the three A copies would therefore solve the reverse-A
target. Otherwise A uses all three possible repeat colours, and any B
copy shares one of them; one A and that B supply the bicoloured corners,
while the Z sources fill the tricoloured corners. This also solves.

Consequently z≤3.

### Reducing to two exceptional supports

Put u=h+z. Suppose u≥2. Then u≤6 and v=11−u≥5. Let R⊆Q be the
rows met by the P/N sources in the reverse 0-column. Since only P_i is
confined to a single row and its count is at most3, |R|≥2.

We first record a small completion fact. If i,j∈R, three distinct P/N
sources can fill i0,j0 and one forward corner of the rectangle on i,j.
To apply Hall, regard the last position as a flexible slot accepting
any source with either1i or1j. Its degree is v−n_k≥2, where k is the
third row. The first two positions have positive degree, and their
union has degree v−p_k≥2. The flexible slot together with either
0-column position sees every P/N source, by the complementary pattern
in Section1. Thus Hall holds. Three A fill the other forward positions.

If the u sources can match two distinct reverse 1-column positions
whose rows lie in R, the preceding completion gives an opposite target.
For |R|=3 they always can. For R={i,j}, every such source meets at
least one of these rows, and u≥2, so failure forces all of them to
miss one row, say j.

All zero sources are then Z_j, and H can occur only if j=4. Every one
of these u sources meets rows i,k, where k is outside R. If z>0 and
u≥3, use a Z_j at k0 and two other u-sources at i1,k1. Two distinct
P/N sources supply i0 and one forward corner of the i,k rectangle:
the former has positive degree, the latter has degree v−n_j≥2, and
their union contains all v sources. Three A complete the forward half.

There remain just two possibilities.

* u=2. Then v=9. Because the 0-column support is R={i,j}, the only
  possible P/N classes are P_i,P_j,N_k, so each has count3.
* z=0 and h≥2. Then j=4, v=11−h≥8, and the same three classes
  P_i,P_j,N_k are the only possibilities. All are present, and at
  least one of P_i,P_j has count3.


## 2. The two exceptions need no all-private assumption

Whenever `A,P_i,P_j,N_k` are present, both `P_i` and `P_j` have
at most one private corner. For `P_i`, A covers its 1-row corners,
`P_j` covers `10`, and `N_k` covers `i0,ik`, leaving at most `ij`.
The statement for `P_j` is symmetric. The nonprivate-triple lemma
therefore makes either of these classes an own-loop class if its
count is three.

The first exception has two such triples. It contradicts the
two-own-loop-triple exclusion.

In the second exception, `h=2` likewise makes all three common
classes triples, giving the same contradiction. Thus `h=3` and
their counts sum to eight. If both `P_i,P_4` are triples, again
there are two own-loop triples. Otherwise `N_k` is a triple and
exactly one of `P_i,P_4` is a triple, with the other doubled.

If `P_4` is that triple, its own loop conflicts with the present
class `H=C(023)`, which has the same pole pair `14`. The looped
triple uses all three allowed repeated colours; H has no other
allowed repeated colour. This is impossible.

If `P_i` is the triple, its own loop uses all three repeated
colours outside its poles `1i`. Both A and H have pole pairs
meeting `1i`, so own-loop restoration makes them conflict with
`P_i`. Each A and each H must consequently repeat `i`.
Reserve one A and one H for an A target's bicoloured corners.
Its six tricoloured corners have the completion

\[
 A:02,03;\qquad H:04;\qquad P_4:1i;\qquad
 N_k:1k;\qquad P_i:14.
\]

All six sources remain available: A and H originally have three
copies each, and the other three classes are present. This is a
solution, another contradiction.

Thus `u<=1`, and hence `v>=10`.

## 3. Ten common-corner sources are now impossible

If all six P/N classes occur, the common-corner nine-cube theorem
applies. At most three present classes have capacity at most nine.
It remains to consider four or five present common-corner classes.

With five classes present, every one has at most one private
corner even within this family. Thus every triple among them has
an own loop, and at most one can be a triple. Their total is at
most eleven.

If the total is eleven, the counts are `3,2,2,2,2`; these five
repeated classes, together with A, violate the six-repeated-class
bound. If the total is ten and there is no triple, all five are
doubled, giving the same contradiction. The only remaining
profile is `3,2,2,2,1`, which always solves by
`common-corner-32221-hand.md`.

With exactly four common-corner classes present, at most one has
two private corners after A is included. Here is the two-absence check. In the common-corner family,
P_i has private arcs $i\to j,i\to k$ only when $N_j,N_k$ are
absent; if only $N_j$ is absent, a second private arc $1\to j$
also requires $P_k$ absent. The dual statements hold for N_i.
The additional class A supplies every $1\to q$, removing that
second P-type arc. If both absent classes are N-types, only the
complementary P-type can retain two private corners; the dual holds
when both are P-types. With one absent type of each kind, at most
one N-type retains two. Hence at most one triple can lack an
own loop. Since there is at most one own-loop triple as well,
the total is at most `3+3+2+2=10`.

Equality is required by `v>=10`. The profile is therefore
`3,3,2,2`, and at least one of its two triples has an own loop.
The lemma `../mixed_diffuse/common-corner-3322-own-loop-hand.md`
excludes exactly this case.

All possibilities have been excluded, proving the row-pair lemma.

## 4. Consequence for every non-own-loop triple

The nonprivate-triple lemma gives at least two private corners
to every triple without an own loop. Three private corners in
a two-row array would put two in one row, which has just been
excluded. Thus such a triple has exactly two private corners.

In particular `private-pair-promotion-hand.md` now applies to
every non-own-loop triple in a failing pure fourteen-pool: its
four nonprivate corners have an outsider matching, and adjoining
any source meeting a private corner creates an own loop.
