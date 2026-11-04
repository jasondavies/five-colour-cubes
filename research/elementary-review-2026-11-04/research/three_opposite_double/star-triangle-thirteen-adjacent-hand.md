# The star-and-triangle family with two opposite cubes

4 November 2026

**Status: complete hand argument; independent root and alternative-agent
mathematical audits passed.**

**Theorem.** Take two arbitrary opposite-repeat cubes, with no
restriction on whether their varieties coincide, and thirteen
adjacent-repeat cubes. Suppose every adjacent tricoloured-corner
class occurs at most three times, and all adjacent classes belong to

    C(01), C(02), C(03), C(04), C(034), C(024), C(014).

Then the pool contains an eight-cube assembly of a five-colour target.
The same statement holds after any colour permutation or simultaneous
reversal of all directed corners.

The proof uses the common-corner eleven-source theorem from
`common-corner-eleven-hand.md` and the nine-source construction in
Section 2 of `../three_opposite_root/repeated-colour-closures.md`.
All other steps are direct constructions or a six-position Hall
argument. No inventory search is a premise.

## 1. Notation and the common-corner reduction

Let I={1,2,3}, and write

    P_i=C(0i), R=C(04), Q_i=C(04i)    (i in I).

Their multiplicities are p_i,r,q_i, respectively. Each lies between
zero and three, and

    p_1+p_2+p_3+r+q_1+q_2+q_3=13.

Put s_i=p_i+q_i and p=p_1+p_2+p_3. The two opposite sources are
O_1,O_2. An opposite source supplies both directions of every edge
of its four-cycle. We write {a,b}|{c,d} for the opposite target whose
underlying edges join these two pairs.

Every class except P_i,Q_i supplies corner0i. Consequently s_i≤2
would give at least eleven adjacent sources with common corner0i,
which assemble by the common-corner theorem. For the remainder,
suppose the pool fails. Then

    s_i≥3 for every i in I.                              (1)

Also p≥1, because the four classes R,Q_1,Q_2,Q_3 have total
capacity twelve.

## 2. A positive class and an opposite edge

**Lemma.** Under (1), suppose p_j>0 and an opposite source O supplies
edge4k, where j,k are distinct members of I. Then the pool assembles.

Let i be the third member of I. Use target {4,i}|{j,k}. Put one P_j
source atj4 and O atk4. The other six target positions are

    ij, ik, ji, ki, 4j, 4k.

They will be filled entirely by the twelve remaining adjacent
sources. Define the three disjoint source groups

    G_i = all P_i and Q_i sources;
    G_j = all P_j and Q_j sources after the P_j reservation;
    G_k = all P_k and Q_k sources.

Their sizes are s_i,s_j−1,s_k, hence at least3,2,3, respectively.
The complete neighbourhoods of the six positions are

| Positions | Adjacent-source neighbourhood after the reservation |
| --- | --- |
| ij, ik | G_i |
| ji | G_j |
| ki | G_k |
| 4j | R, Q_i, Q_k |
| 4k | R, Q_i, Q_j |

Here a class name denotes all its available copies. In particular,
the reservation of P_j changes neither of the last two rows.

We check Hall's condition for every subset of these six positions.
Call ij,ik,ji,ki the first four positions and 4j,4k the last two.

* A subset containing no first position consists of one or both last
  positions. Each last position has at least one neighbour: for
  example, if r=q_i=q_k=0, only P_1,P_2,P_3,Q_j could occur, whose
  total capacity twelve contradicts the original count thirteen.
  The two last positions together have

      r+q_1+q_2+q_3=13−p≥4

  neighbours.

* If the subset meets at least two of the three first-position
  groups {ij,ik}, {ji}, {ki}, their disjoint source groups alone
  supply at least five neighbours. A subset meeting exactly two
  groups has at most five positions. A subset meeting all three
  groups has at most six positions and at least3+2+3=8 neighbours.

* Suppose the subset meets only {ij,ik} among the first-position
  groups. If it uses at most one last position, it has at most three
  positions and at least s_i≥3 neighbours. If it uses both last
  positions, its neighbour count is

      s_i+r+q_j+q_k=13−p_j−p_k≥7.

* Suppose the subset meets only {ji}. With at most one last position
  it has at most two positions and at least s_j−1≥2 neighbours. With
  both last positions it has

      (s_j−1)+r+q_i+q_k=12−p_i−p_k≥6

  neighbours. If it meets only {ki}, the same argument uses s_k≥3
  and, when both last positions occur,

      s_k+r+q_i+q_j=13−p_i−p_j≥7.

This exhausts the subsets. The six-position matching, together with
the two reserved sources, proves the lemma.

For any opposite source O put

    N_4(O)={k in I : O supplies edge4k}.

Since p≥1, the lemma implies the following restriction in a failure:
either N_4(O) is empty, or it is a singleton {s} and every positive
P_j is P_s. Indeed, two members of N_4(O) would give a member
different from any chosen j with p_j>0. Moreover N_4(O) is empty
exactly when O omits colour4. If N_4(O)={s}, the two neighbours of4
in O are0,s.

## 3. Two different non-4 neighbours of0

**Lemma.** Under (1), suppose O_1,O_2 can be assigned to edges0i,0k
for two distinct i,k in I. Then the pool assembles.

Let j be the third member of I and use target {0,j}|{i,k}. Put the
opposite sources ati0,k0. The remaining six positions are filled as
follows:

| Sources | Assigned corners |
| --- | --- |
| Two sources from P_j,Q_j | ji, jk |
| Two sources from P_i,Q_i | ij, 0k |
| Two sources from P_k,Q_k | kj, 0i |

Every source in a row supplies both listed corners. Each row has at
least three sources by (1), so all six chosen sources are distinct.
This proves the lemma.

Now apply both lemmas to a hypothetical failure. An opposite source
omitting4 has two neighbours of0 in I. Any other opposite source
allowed by Section 2 either also omits4, or has neighbours0,s at4
and therefore has a further neighbour t in I at0. In either case
the two sources can be assigned to distinct edges0i,0k. Thus neither
opposite source can omit4 in a failure.

Both N_4(O_1),N_4(O_2) are therefore singletons. Since some P_j
occurs, they must have the same member s, and only P_s can occur.
Each opposite has a further neighbour t in I at0. These two
neighbours must coincide, by the second lemma. Also t≠s, since the
four-cycle has edges04,4s and cannot close using only three vertices.
Both opposite sources are consequently the same four-cycle

    O={04,4s,st,t0}.                                      (2)

Let u be the third member of I.

## 4. The last multiplicity reduction

We have p_t=p_u=0. Since s_t,s_u≥3 and each class has cap three,

    q_t=q_u=3.

The remaining count equation is

    p_s+r+q_s=7,      1≤p_s≤3, r≤3, q_s≤3.               (3)

In particular q_s≥1.

If p_s≥2, use the opposite target {0,s}|{4,t}. There is the explicit
assembly

| Sources | Assigned corners |
| --- | --- |
| The two O sources | 40, t0 |
| Two P_s | 04, s4 |
| One Q_t | ts |
| One Q_s | st |
| Two Q_u | 0t, 4s |

The eight corners are distinct and are exactly those of the target.
The indicated source multiplicities are available by (3), and every
incidence follows directly from the relevant cut or from (2).

Therefore a failure would require p_s=1. Equation (3) then forces
r=q_s=3. The whole pool has the form

    2O + P_s + 3R + 3Q_s + 3Q_t + 3Q_u,                 (4)

with O given by (2).

## 5. The repeated-colour completion

The nine-source subpool

    O + 3Q_s + 3Q_t + 2R

already assembles. Indeed, O supplies edgest. Simultaneous reversal
sends

    Q_s=C(04s) to C(tu),
    Q_t=C(04t) to C(su),
    R=C(04)   to C(stu),

and leaves the bidirected corners of O unchanged. Thus the reversed
subpool is precisely the previously proved nine-source construction

    O(edge st) + 3C(tu) + 3C(su) + 2C(stu).

This contradicts failure in (4) and proves the theorem. Equivalently,
Q_s and Q_t are own-looped triples with intersecting pole pairs tu
and su, so their repeated colours give the completion.

## 6. Proof dependencies and scope

The proof is uniform in the two original opposite varieties and in
all actual repeated colours within every adjacent class. It assumes
only the cap of three on adjacent tricoloured-corner classes.

Its two earlier inputs are:

1. the theorem that eleven adjacent sources with a common directed
   tricoloured corner and class cap three assemble;
2. the nine-source union-class construction, including simultaneous
   reversal.

Both inputs have independently audited hand proofs. The two new
matching lemmas and the multiplicity reduction above have passed
independent root and alternative-agent mathematical audits. The latter
is recorded in `../elementary_alternative_next/audit-star-triangle.md`.
No exhaustive search or new formalisation is used.
