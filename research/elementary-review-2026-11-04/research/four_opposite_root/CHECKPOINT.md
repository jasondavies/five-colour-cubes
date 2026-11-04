# Four-opposite target: completed checkpoint

3 November 2026

**Completed statement:** four opposite sources with variety cap two,
plus ten adjacent sources with tricoloured-corner class cap three,
always contain an eight-source five-colour target assembly.

The master proof and exact scope are in
`../root/four-opposites-ten-adjacent.md`. This checkpoint supersedes
the exploratory status in `../four_opposite_computation/RECON.md` and
the discovery JSON files in the four-opposite directories.

## Completed proof components

| Component | Proof file | Review status |
| --- | --- | --- |
| Four distinct opposite varieties | `../four_opposite_lowrep/four-distinct-opposites.md` | Full independent root audit passed. |
| Four capped opposite sources on a line | `../four_opposite_pairs/neighbouring-pairs-four-classes.md` | Full independent root audit passed. |
| Nonneighbouring pairs: missing path and first two orientations | `../four_opposite_computation/missing-path-and-two-orientations-hand.md` | Full independent root audit passed. |
| Nonneighbouring pairs: alternating orientation and repeated colours | `../four_opposite_pairs/alternating-path-family.md` | Full independent root audit passed. |
| One-double global adjacent-zero-edge lemma | `../four_opposite_lowrep/one-double-zero-edge.md` | Root and separate independent audits passed. |
| One-double exceptional adjacent-edge pair | `../four_opposite_pairs/one-double-zero-edge-endpoint.md` | Full independent root audit passed. |
| One-double exceptional end-edge pair | `../four_opposite_lowrep/zero-center-opposite-pattern.md` | Full independent root audit passed. |
| One-double common-high reduction and four-cycle exhaustion | `common-high-targets.md` | Final independent audit passed; see `common-high-audit.md`. |

The final audit corrected one phrase about Hall neighbours on the two
edges not met by the doubled variety. The corrected claim concerns
subsets meeting both edges. Subsets on one edge were already handled
by the preceding one-edge bound. No new missing case was found.

## What is and is not proved

The argument is elementary and does not use exhaustive inventory
enumeration as a premise. Individual cut lists and explicit small
matching tables are part of the written geometric proof. Diagnostic
searches and checkers are retained for reproducibility and were not
converted into a new Lean certificate.

Combining with earlier results covers every fifteen-pool with at least
four opposite sources. It also completes the fourteen-failure
classification at opposite total four: all four opposite sources have
one variety and the adjacent class profile is 5,5, giving W=36.

The full elementary N5=15 theorem still has diffuse opposite totals
one, two and three outstanding, with opposite variety cap two and
adjacent class cap three. For the global fourteen-failure identity,
the unique-own-loop pure branch is additionally outstanding.

The next uniform target is three opposite sources plus eleven
adjacent sources under those same caps. No result for that target is
claimed by the present checkpoint.

The production repository was not modified.
