# Independent audit of the star-and-triangle branch

4 November 2026

**Outcome: PASS.** This is an independent mathematical audit of
`../three_opposite_double/star-triangle-thirteen-adjacent-hand.md`.
Every Hall subset type, count reduction, opposite-source restriction,
and physical-source allocation was checked. No inventory enumeration
was needed for this audit.

## 1. Common-corner reduction and the six-position Hall lemma

For I={1,2,3}, the classes are P_i=C(0i), R=C(04), Q_i=C(04i).
Precisely P_i,Q_i miss the corner0i. Hence s_i=p_i+q_i≤2 leaves
at least eleven sources through0i. After excluding that case using
the audited common-corner lemma, all s_i≥3. Also at least one P_i
occurs, because R and the three Q classes have capacity twelve.

For p_j>0 and an opposite supplying4k with j≠k, the reservations
P_j:j4 and O:k4 on target{4,i}|{j,k} are valid. The six remaining
corners are ij,ik,ji,ki,4j,4k. Their displayed neighbourhoods are
exact; in particular the P_j reservation affects G_j only and does
not affect either4-row neighbourhood.

The Hall argument covers all subsets:

- With no first-group positions, either singleton4j/4k is supported
  by the thirteen-source count and four-class capacity twelve. The
  pair has13−p≥4 neighbours.
- At least two first groups supply at least five neighbours, enough
  for every subset meeting exactly two groups. All three supply
  at least eight, enough for all six positions.
- The group{ij,ik} alone supplies three neighbours for subsets using
  at most one last position. With both last positions its union has
  13−p_j−p_k≥7 neighbours.
- The group{ji} has s_j−1≥2 neighbours after the reservation.
  With both last positions its union has12−p_i−p_k≥6.
- The group{ki} has s_k≥3 neighbours, and with both last positions
  its union has13−p_i−p_j≥7.

Thus the six-position matching exists with distinct adjacent sources.
The reserved P_j and opposite are separate physical sources, so
this indeed gives an eight-source assembly.

## 2. Restrictions on the opposite sources

An opposite containing4 has degree two there, and at least one of
its neighbours lies in I. Therefore N_4(O)=∅ is equivalent to
omitting4. If N_4(O) has two members, the first lemma applies with
any positive P_j and one of the two members distinct from j.
If N_4(O)={s}, every positive P_j must have j=s, and the other
neighbour of4 is0. These are exactly the claimed alternatives.

The second lemma assigns two distinct opposite sources to i0,k0
and two adjacent sources from each of G_i,G_j,G_k to the displayed
six corners. Each class in each group supplies both listed corners.
The groups are disjoint and have sizes at least three. The argument
allows the two opposite varieties to coincide.

An opposite omitting4 has two neighbours of0 in I. Any other
opposite surviving the first restriction has at least one such
neighbour. The two sources can then be assigned to distinct I-neighbours
of0, so neither may omit4 in a failure.

The nonempty positive P support forces both singleton N_4 sets to
have the same member s. Their further neighbours t of0 must also
coincide, or the second lemma applies. A simple four-cycle forces
t≠s. Hence the identical cycle04–4s–st–t0 is the entire residual,
with no unproved normalization or marked-single assumption.

## 3. Multiplicities and final repeated-colour core

The restrictions p_t=p_u=0 and s_t,s_u≥3 force q_t=q_u=3.
The equation p_s+r+q_s=7 then gives q_s≥1. For p_s≥2,
all eight entries in the displayed{0,s}|{4,t} assignment are
correct, distinct, and use no source class beyond its available count.

For p_s=1, the cap forces r=q_s=3. The subpool

    O +3Q_s+3Q_t+2R

is therefore available. The reversal to the previously audited
nine-source union-class construction is exact. It can also be
checked directly by the following own-loop matchings, made after
reserving two copies of the indicated target class:

| Target | Remaining target copy | Other triple | Two R sources | O |
| --- | --- | --- | --- | --- |
| Q_s | su | Q_t:0u,4u | 0t,4t | st |
| Q_t | tu | Q_s:0u,4u | 0s,4s | ts |

Each row supplies precisely its six tricoloured target corners.
The pole pairs tu and su meet at u. If either triple repeats a
colour twice, its own loop solves. Otherwise both use all three
allowed repeats, share a repeat, and universal restoration gives
the two-class bicoloured completion. This is a local nine-source
argument, independent of the fifteen-cube theorem.

All branches of the star-and-triangle proof are therefore complete.
