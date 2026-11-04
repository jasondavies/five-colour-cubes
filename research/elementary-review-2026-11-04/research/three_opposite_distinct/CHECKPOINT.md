# Three-distinct-opposite branch checkpoint

4 November 2026

## Completed theorem

Three pairwise distinct opposite sources plus eleven adjacent sources
of class cap three always assemble a five-colour target.

The master proof is `three-distinct-eleven-adjacent.md`. Its four
components are:

1. `global-zero-edge.md`: a globally absent adjacent underlying edge
   gives an opposite assembly, for any three distinct opposite sources.
2. `rectangle-family.md`: any three distinct varieties high on one
   target, with eleven adjacent sources confined to one directed half
   of that target, give an assembly. Full opposite support is not needed.
3. `unsupported-triad.md`: the unique unsupported common-high-target
   geometry is closed by small Hall tables and a displayed intersection
   certificate.
4. The independently developed common-corner eleven-source theorem in
   `../three_opposite_double/common-corner-eleven-hand.md`.

All three local components, the common-corner theorem, and the master
joining argument passed independent root mathematical audits. The
root's additional small geometric checker is
`../three_opposite_root/audit_unsupported_triad.py`.

No inventory enumeration is a premise. The final triad certificate
contains only small corner sets and finite cut-set intersections.
The conclusion is existence of some five-colour target, because the
common-corner step may use repeated colours and an adjacent target.
The stronger exploratory opposite-target observation is not needed.

## Additional direct-fifteen branch

`two-star-two-opposites.md` proves that thirteen adjacent sources in
the two-star family C01,C02,C03,C04,C034,C024,C023, with class cap
three, together with any two opposite sources assemble. Its main
new case is 3C01 plus ten common-corner01 sources. This has a direct
opposite-target matching proof, including identical opposite sources.
The full note passed its independent root audit, including all Hall
conditions, source allocations, and the completeness of the cases.

The sibling profile2,1 proof, one-opposite fifteen-source proof,
and the butterfly and star-and-triangle two-opposite proofs are now
complete and independently audited. The parent has joined all three
opposite profiles in `../root/three-opposites-eleven-adjacent.md`, and
compression plus the three intersecting families in
`../root/two-opposites-thirteen-adjacent.md`.

## Final synthesis and independent audits

`../root/fifteen-elementary-proof.md` is the complete direct threshold
proof assembled from those component lemmas. Its final independent
joining audit passed; see
`../three_opposite_double/audit-fifteen-elementary-master.md`.
Its shorter case split uses the three-opposite
theorem for opposite totals three and four, and the five-opposite
helper theorem for totals five and six. The stronger four- and
six-opposite fourteen-source theorems remain independent results.

The independent audits performed in this directory are:

- `audit-root-replacement-and-nine-core.md`: disjoint-pair compression,
  the three-family containment classification, and the nine-source
  repeated-colour core all pass.
- `audit-butterfly-two-opposites.md`: the complete butterfly family
  theorem, including actual-source bookkeeping, passes.

`direct-fifteen-dependency-outline.md` is the earlier historical
planning checkpoint; the final master supersedes its open-case list.
The global fourteen-failure identity is still a separate open
question, with exact remaining scope recorded in the final master.

## Diagnostic files

`hall_family_explore.py` and its output helped discover the compact
rectangle proof; they are superseded by its direct allocations.
`triad_hall_explore.py` and its output found the small triad Hall
certificate, whose full mathematical reduction and tables are now
written in `unsupported-triad.md`.
