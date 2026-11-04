# Eight cubes with a common missing pair and three additions

4 November 2026

**Status: complete, independently audited hand proof.** The audit
checked the projection cases, cell and row neighbourhood bounds,
all survivor counts, and the final three-source Hall matching.

This is a self-contained version of the paper's independent
eight-plus-three lemma, included so the elementary-proof bundle does
not depend on a file outside the archive. It is the same local result
as `lem:eight-common-missing` in `paper/boxes.tex` at repository commit
`1dce44d24f76e84f0266025ab9ce0ab94a306873`. The projection calculation
below is written directly in the cut model. No corner threshold is
assumed.

## 1. The family and its corner array

Fix a missing bichromatic edge pair, normalized to 01. Let
P={0,1} and R={2,3,4}. In a cube missing edge type 01, the 0 and 1
faces are opposite singleton faces. The other four faces use the
three ring colours, one twice. Thus the family consists of:

- three varieties in the adjacent class C(P), one for each repeated
  ring colour;
- three varieties in the reverse adjacent class C(R);
- three opposite varieties with bipartition P|{i,j}, where i,j
  are two of the ring colours.

Write C⁺=C(P) and C⁻=C(R) for the two sets of six tricoloured
corners. Every family opposite variety has four corners in each.

Fix the family opposite target P|{i,j}. Its eight corners form a
two-by-two array with two positions per cell: the rows correspond
to i and j, and the columns to C⁺ and C⁻. The target variety itself
meets all four cells. Each of the other two family opposite varieties
meets one row; positive and negative adjacent varieties meet their
respective columns. Both positions in a cell have the same source
neighbourhood within the family.

## 2. The projection calculation

For a source W, let p(W),m(W) count its tricoloured corners in C⁺,C⁻.
The family varieties have pairs (6,0), (0,6), and (4,4).

For an adjacent source with outset S, put x=|S∩P| and y=|S∩R|.
The cut definition gives directly

    p(W)=x(3−y),       m(W)=y(2−x).

The constraints |S|=2 or3 give, outside the two family classes,
exactly the four possibilities

    (4,0), (2,1), (1,2), (0,4).

For an opposite source, p(W)=m(W) is the number of edges of its
four-cycle crossing P and R. A family opposite has four such edges.
Any other opposite has two: if one pole is omitted, its other pole
has degree two into R; if both poles occur, they must be adjacent
in the cycle unless it is a family variety. Thus outside the family
the only additional pair is (2,2).

Consequently every source satisfies the implications

| Bound on p(W) | 0 | 1 | 2 |
| --- | ---: | ---: | ---: |
| Lower bound on m(W) | 4 | 2 | 1 |

## 3. The theorem

**Theorem.** Eight sources from this missing-pair family, together
with any three other five-colour sources, contain a corner assembly
whose target belongs to the same family.

Let O,P₀,Q₀ count the opposite, positive-adjacent and negative-adjacent
sources among the chosen eight, so O+P₀+Q₀=8.

First suppose O+min(P₀,Q₀)≥4. Choose a family opposite target whose
opposite-variety multiplicity among the eight is maximal. The corner
array in Section 1 satisfies Hall's inequalities: every cell has at
least O/2+min(P₀,Q₀)≥2 neighbours; every row has at least 8−O/2≥4;
and every column has at least O+min(P₀,Q₀)≥4. Every other union of
cells has all eight sources as neighbours. A subset partly filling
a cell has the same neighbours as that cell and fewer requirements,
so these inequalities give a matching of all eight corners.

Otherwise exchange the signs so that κ=O+Q₀≤3. Then P₀=8−κ≥5.
One of the three positive varieties occurs at least twice. Use that
variety as an adjacent target. If its corners match in the full pool,
we are done. Otherwise choose a deficient Hall set D of its corners.
The two copies of the target variety are universal, so |D|≥3 and D
contains a tricoloured corner. All P₀ positive sources meet D.

Let E be the other source neighbours of D. Put U=C⁺\D and u=|U|.
There are only two bicoloured target positions, so |D|+u≤8. Hence

    P₀+|E|<|D|≤8−u,       |E|+u≤κ−1.

Remove all P₀ chosen positive sources and the sources in E. Every
survivor has its positive corners contained in U, and u≤2. No chosen
family opposite source can survive, because it has four positive
corners. At least κ−|E|≥u+1 of the chosen nonpositive sources survive,
and all these are negative-family sources, universal on C⁻. The
total surviving pool has size at least κ+3−|E|≥4+u.

Partition C⁻ into its three pairs {i0,i1}, i in R. The negative
half of a family opposite target is the union of two such pairs.
We will match one four-position half in the surviving pool; four
of the removed P₀ positive sources will then fill its positive half.

Let j be the number of negative-family sources among the survivors,
including any among the three additions. We have j≥u+1.

- If j≥4, four such sources fill any negative half.
- If j=3, at least one further survivor exists. It has a negative
  corner by Section 2. Choose a half containing that corner and
  use the three negative-family sources at the other positions.
- If j=2, then u≤1. At least two further survivors exist and each
  has at least two negative corners. They can be assigned distinct
  corners, which lie in the union of at most two of the three pairs.
  Choose that target half; the two negative-family sources finish it.
- If j=1, then u=0. At least three further survivors each have at
  least four of the six negative corners. Choose one W and a union
  of two pairs containing at least three of its corners. Every other
  survivor meets that four-position half in at least two positions.
  Thus W and any two other survivors match three distinct positions:
  each two-source set has at least two neighbours and the three-source
  union has at least three. The negative-family source fills the fourth.

In every case four survivors fill a negative half. Four of the
P₀≥5 removed positive sources fill its positive half. These are
eight distinct actual sources, giving the asserted assembly.

## Provenance and scope

The original family-array and projection lemmas are in the user's
paper. This cut-model presentation supplies their full local proof
and the eight-plus-three argument within the research bundle. Its
only ingredients are the cube corner model, the displayed projection
formula, Hall's theorem, and elementary counting. In particular,
neither N₅=15 nor any fourteen-cube failure classification is used.
