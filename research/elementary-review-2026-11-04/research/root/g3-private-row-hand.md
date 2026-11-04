# A row of private corners is impossible in the all-private branch

**Elementary conditional lemma.** Consider a failing pool of fourteen
adjacent-repeat cubes, with every tricoloured class of size at most
three. Suppose every class of size three has at least two corners
private to that class. Then no class of size three has two private
corners in one row of its two-by-three cut array.

The proof uses the six-repeated-classes corollary in
`six-doubled-classes-hand.md` and the common-corner nine-cube lemma in
`../pure_supported/common-corner-nine-hand.md`. It does not assume that
the all-private branch has already been classified.

## 1. The eleven possible outsider classes

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

## 2. At most three zero-intersection sources

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

## 3. Two sources meeting the reverse 1-column force a solution

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

Both contradict the private-corner hypothesis. For P_i, the presence
of A, P_j and N_k leaves at most the corner ij private: A supplies
its 1-row corners, P_j supplies10, and N_k supplies i0 and ik.
The same argument applies to P_j. Hence u≥2 is impossible.

## 4. The remaining common-corner mass is too large

We have u≤1 and hence v≥10 in the six-class common-corner family.
If all six classes are present, the common-corner nine-cube lemma solves.
If at most three are present, their capacity is9.

With five present classes, every class has at most one private corner
even within this family. Thus none can have multiplicity3, and v≤10.
Equality gives five doubled classes; with A this makes six repeated
classes in the fourteen-pool, already excluded by the six-repeated-
classes theorem.

Finally suppose exactly four common-corner classes are present. At
most one of them can have two private corners after A is included.
Here is the full two-absence check, writing a=1 and b=0 for the common
corner ab. In a common-corner family, P_i has
potential private arcs i→j and i→k when N_j and N_k are absent; with
only N_j absent, a second private arc a→j requires P_k absent.
The dual statements hold for N_i. Our extra class A contains every
arc a→q, q∈Q, removing that second P_i arc. If the two absent classes
are both N-types, only the complementary P-type can have two private
corners; if both are P-types, only the complementary N-type can.
If one of each is absent, at most one N-type retains two private
corners. Thus at most one present class has count3, and v≤3+2+2+2=9.

Every possibility contradicts v≥10. This proves the conditional lemma.
