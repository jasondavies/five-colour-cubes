# Two opposite cubes and thirteen adjacent cubes in the two-star family

4 November 2026

**Status: elementary proof; full independent root audit passed.**

**Theorem.** Let thirteen adjacent sources, each class occurring at
most three times, belong to

    C(01), C(02), C(03), C(04), C(034), C(024), C(023).

Together with any two opposite sources, which may have the same
variety, they contain a five-colour assembly.

Put A=C(01). Every other listed class contains the directed corner01.
If at most two A sources occur, at least eleven adjacent sources
share01, and the common-corner eleven-source lemma applies. Hence
it suffices to prove the following stronger special statement:

> Three A sources, ten capped adjacent sources containing01, and
> any two opposite sources contain an opposite-target assembly.

Write Q={2,3,4} and name the six common-corner classes

    P_i=C(0i), D_i=C({0}∪(Q\{i})), for i∈Q.

The ten-source common-corner pool will be called B. Its class cap is
three. All constructions below use only tricoloured corners, so its
repeated colours are irrelevant.

## 1. An opposite source omits colour0

Use that source's own target, whose parts are {1,i} and {j,k},
where {i,j,k}=Q. Two A copies fill1j,1k. The other six target
positions form J, and the B intersections with J are:

| Class | Positions in J |
| --- | --- |
| P_i | ij,ik |
| P_j | j1,ji |
| P_k | k1,ki |
| D_i | j1,ji,k1,ki |
| D_j | ij,k1 |
| D_k | ik,j1 |

The five two-position patterns are the edges of the path

    ji — j1 — ik — ij — k1 — ki.

The four-position pattern D_i consists of the first two and last
two positions of this path.

The ten B sources have matching rank at least five on J. To prove
this, suppose a Konig cover has at most four vertices. Four corner
vertices contain at most three of the six patterns: if they contain
D_i they are exactly its four positions and contain only the two
end path edges besides it; otherwise four vertices of a path contain
at most three edges. Their class capacity is therefore at most nine.
Three corner vertices contain at most two path edges, hence six
copies, and at most one extra source vertex is allowed. Two corner
vertices contain at most one edge, hence three copies, with at most
two extra source vertices. One or no corner vertices contain no
complete source pattern. Every case fails to cover ten sources.

Match five B sources to five positions of J. The opposite source is
universal on its own target and fills the remaining position. With
the two A copies this is an assembly. The second opposite source
and the third A copy are unnecessary in this case.

## 2. Two different incoming corners at0

Now suppose neither opposite source omits0. If they can supply
incoming corners i0,j0 for distinct i,j∈Q, choose those assignments
on the target with parts01 and ij. Let k be the third colour of Q.

The B sources can fill i1,j1 and one position from {0i,0j}, using
three distinct sources. This is a three-requirement Hall matching:

- i1 is supplied by P_i,D_j,D_k. Its complementary three classes
  have total capacity nine, so at least one of the ten sources
  supplies it. The same holds for j1.
- At least seven sources meet {0i,0j}, since only D_k misses both.
- At least seven sources meet {i1,j1}, since only P_k misses both.
- Each pair consisting of the forward requirement and one incoming
  requirement meets every B source, as does the full three-set.

Thus all Hall inequalities hold. After those three B assignments,
three A copies fill the other three positions of the forward
rectangle. Together with the two opposite assignments i0,j0,
this assembles the target.

## 3. The remaining opposite-source shape

Both opposite sources contain0. Each has at least one neighbour of0
in Q, because it has degree two and only one other possible neighbour
is1. If Section 2 does not apply, their neighbour sets in Q are
both the same singleton {i}. Thus both contain the edges01 and0i.
This includes identical opposite varieties.

Let j,k be the other two colours of Q. Consider either target

    T_j={0,j}|{1,i},   T_k={0,k}|{1,i}.

On T_j, put the two opposite sources at10,i0 and two A sources at
0i,1j. The remaining positions are01,j1,ji,ij. Write the B counts as

    a=g(P_i), b=g(P_j), c=g(P_k),
    d=g(D_i), e=g(D_j), f=g(D_k),

with a+b+c+d+e+f=10 and each count at most three. The three
nonuniversal remaining positions have neighbourhood counts

    ji: b+d;  ij: a+e;  j1: b+d+f.

Their matching exists exactly when

    b+d≥1,  a+e≥1,  b+d+f≥2.                   (J)

The pair {ji,j1} gives the last inequality; the other Hall
inequalities follow from the first two and the disjointness of
the class groups supplying ij and ji,j1. After these three sources
are used, any unused B source fills01.

Likewise T_k assembles if

    c+d≥1,  a+f≥1,  c+d+e≥2.                   (K)

Conditions (J) and (K) cannot both fail:

- If b+d=0, then b=d=0. Capacity gives c>0, since a+e+f≤9.
  Also a+f≥4 and c+e≥4, because each complementary pair of
  classes has capacity six. Thus (K) holds.
- If a+e=0, then a=e=0. Now f>0, since b+c+d≤9, and
  c+d≥4, since b+f≤6. Again (K) holds.
- Otherwise b+d≥1 and a+e≥1. Failure of the third condition
  in (J) forces b+d=1 and f=0. The remaining counts satisfy
  a+c+e=9, so a=c=e=3. Every condition in (K) follows.

Hence one of T_j,T_k assembles. Sections 1–3 exhaust every pair
of opposite varieties, proving the stronger special statement and
therefore the two-star-family theorem.

## Scope and dependencies

Only the first reduction uses the common-corner eleven-source
theorem from
`../three_opposite_double/common-corner-eleven-hand.md`. The
three-A, ten-common-corner construction is a direct matching proof
independent of that theorem, of the three-opposite result, and of
any exhaustive inventory classification.
