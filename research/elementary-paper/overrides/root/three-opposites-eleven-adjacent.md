# Three opposite cubes and eleven capped adjacent cubes

4 November 2026

**Status: complete hand proof.** Both diffuse multiplicity branches and
their joining arguments have passed independent mathematical audits.
The concentrated branch uses the earlier elementary classification,
not the exhaustive fourteen-cube failure catalogue.

## Theorem

Take three opposite-repeat five-colour cubes and eleven adjacent-repeat
five-colour cubes. If no adjacent tricoloured-corner class occurs more
than three times, eight of these fourteen cubes assemble a five-colour
2×2×2 cube with monochromatic faces.

There is no restriction on the multiplicities of the three opposite
varieties. The conclusion permits either an adjacent-repeat or an
opposite-repeat target. All sources are physical cubes, and an assembly
uses eight distinct sources with compatible proper rotations.

## Proof by the opposite multiplicities

There are three possibilities.

1. **Three distinct varieties.** Apply the theorem in
   `../three_opposite_distinct/three-distinct-eleven-adjacent.md`.
   Its proof uses Hall's theorem on a common high target. A fully
   supported target reduces to a rank-five matching, a directed
   rectangle, or a common-corner family. The unique unsupported triad
   is handled by displayed small Hall-obstruction tables and their
   set intersections. Each of these component proofs has been audited.

2. **One doubled variety and one different variety.** Apply
   `../three_opposite_double/three-opposites-one-double-hand.md`.
   Hall's theorem on the doubled variety reduces failure to a
   five-position cover. A missing bidirected edge is impossible;
   otherwise the three missing directions form a path. Its monotone,
   one-change, and alternating orientations are all solved in the
   accompanying hand proofs, retaining both possible single varieties
   when a symmetry does not preserve the marked source.

3. **Three identical varieties.** The earlier elementary classification
   in `o3-covers-guide.md` says that a fourteen-cube failure containing
   three identical opposite cubes has adjacent class sizes 5,3,3.
   This contradicts the present adjacent class cap of three.

These cases exhaust the three opposite sources. No inventory search
is a premise of the argument.

