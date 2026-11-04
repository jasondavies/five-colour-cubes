# Three opposite cubes with one doubled variety

4 November 2026

**Theorem.** Let D,P be distinct opposite-repeat five-colour varieties.
Two copies of D, one of P, and eleven adjacent-repeat cubes of
tricoloured-corner class multiplicity at most three contain an
eight-cube assembly of a five-colour target.

This note joins the component hand proofs. The proof does not use
the exhaustive fourteen-cube failure catalogue.

## 1. Reduction to a five-position cover of D

Suppose the pool fails. A triple adjacent class has at most one
adjacent source disjoint from it: the earlier construction using
three diffuse opposite sources, the triple and two disjoint sources
would otherwise assemble.

On target D its two copies are universal, so the other twelve sources
have matching rank at most five. The argument in
`hall-four-cover-hand.md` excludes every König cover with fewer than
five corner vertices, including the four-corner cover with one
exceptional source. Consequently all twelve D-intersections lie in
a five-position set H.

If the complement of H contains a complete bidirected edge,
`five-cover-bidirected-hand.md` gives an assembly. This already
settles neighbouring varieties D,P: their four-position intersection
is two complete edges, so a five-position H containing it necessarily
has a missing complete edge.

## 2. The remaining three oriented-path forms

Only the nonneighbouring case remains. The complement of H consists
of three positions on distinct underlying target edges. These three
edges form the path obtained by deleting the common edge D∩P from
D. The cut restrictions have three geometric forms, up to target
symmetries and simultaneous reversal of directions.

Normalize D={13,14,23,24}. The following table records the three
forms, with every possible single P retained. Thus reversal of the
path is not incorrectly assumed to preserve the marked variety P.

| Form | Absent D corners | Eligible adjacent outsets | Possible P |
| --- | --- | --- | --- |
| Monotone | 24,32,41 | 01;124;14;014 | O67,O72 |
| One change | 24,31,41 | 01;134;124;13;14;014;013 | O64,O73 |
| Alternating | 32,41,42 | 01;02;124;123;12;023;23;012 | O67,O72 |

The cut lists follow by imposing that each absent direction u→v
forbids u in the outset with v outside it. The possible opposite
singles are obtained by closing a four-cycle meeting D only in
the remaining bidirected edge. There are exactly two choices per
edge, listed above.

In the monotone row, all eleven adjacent sources contain corner13.
The elementary theorem in `common-corner-eleven-hand.md` therefore
gives an assembly without using any opposite source.

Both singles in the one-change row are covered separately by
`one-change-path-hand.md`.

The alternating row is covered by `alternating-path-hand.md`.
Its proof handles P=O67. The colour permutation (1 3)(2 4), followed
by reversing all directions, preserves that absent alternating
pattern and D, and exchanges O67 with O72. It therefore covers the
other single as well.

All possible five-position covers have now been excluded. This
proves the theorem.

## 3. Dependency and status

The proof uses the earlier three-opposite/disjoint-source construction,
the two- and three-position cut bounds, the nine-avoider observation,
and the following new component notes:

- `common-corner-eleven-hand.md`;
- `hall-four-cover-hand.md`;
- `five-cover-bidirected-hand.md`;
- `one-change-path-hand.md`;
- `alternating-path-hand.md`.

The last alternating count configuration uses the independent
nine-source construction in Section 2 of
`../three_opposite_root/repeated-colour-closures.md`.

All component notes and this joining reduction have passed independent
root mathematical audits. The two path notes and this joining
reduction have also passed an independent alternative-agent audit,
recorded in
`../elementary_alternative_next/audit-doubled-path-components.md`.
No new Lean formalisation is claimed.
