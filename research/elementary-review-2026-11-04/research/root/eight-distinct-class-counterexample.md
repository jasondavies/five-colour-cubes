# The nine-distinct-class bound is sharp

The theorem in `nine-distinct-hall-proof.md` says that nine adjacent
cubes in distinct tricoloured-corner classes always assemble an opposite
target. Eight do not always assemble even if adjacent targets are allowed.

Write C(S) for the tricoloured cut S→Sᶜ. A source in this class with
repeated colour r has the two bicoloured corners (r,r,p), where p runs
over the two-element side of the cut. Take the following eight sources:

| Name | Tricoloured class | Repeated colour |
| --- | --- | ---: |
| a | C01 | 3 |
| b | C234 | 2 |
| c | C02 | 1 |
| d | C124 | 2 |
| e | C12 | 3 |
| f | C024 | 2 |
| g | C24 | 0 |
| h | C012 | 0 |

All eight classes are different. The following is a direct failure
certificate, independent of an exhaustive catalogue of eight-pools.

## 1. Possible tricoloured target sets

The only directed tricoloured corners missing from the pool are32,34,42.
Thus an adjacent target outset must be an upset of the chain3<4<2,
with0,1 isolated. Its size-two and size-three upsets are exactly the
eight classes in the table.

The only supported opposite targets have parts01 and two of2,3,4.
For target01∣34, corners30 and31 are both available only on b.
For targets01∣24 and01∣23, corners02 and12 are both available only
on a. Each therefore fails Hall.

## 2. The eight adjacent classes

* C01 requires02 and12, both confined to a, so it fails for every repeat.
* C234 requires30 and31, both confined to b, so it also fails.
* C02 can only use repeat1 or3, since other required bicoloured corners
  are absent. With repeat1, its two bicoloured positions are both confined
  to c. With repeat3, its two bicoloured positions force a and e.
  Among the six remaining sources, b,d,g have compatible corners only
  among21 and23, so those three cubes cannot all be placed.
* C124 can only use repeat2. The three physical sources a,c,h then
  have compatible corners only among13 and23. Since all eight physical
  sources would have to be used, these three sources cannot be placed.
* C12 can only use repeat3. Its two bicoloured positions force a and e
  to be used there. Among the six remaining sources, the three
  tricoloured positions10,13,14 have only d,h as neighbours.
* C024 can only use repeat2. The three sources a,e,h have compatible
  corners only among03 and23, again impossible.
* C24 can only use repeat0. Source a has no compatible corner at all.
* C012 can only use repeat0. Source b has no compatible corner at all.

Thus no adjacent or opposite five-colour target can be assembled.

Consequently the following sharpened statement is proved:

> The least number guaranteeing an assembly for adjacent-repeat cubes
> in pairwise distinct tricoloured-corner classes is nine. Nine always
> admit an opposite-repeat target, whereas eight may admit no target.

The attached JSON gives the same pool in the independent corner model,
with Hall witnesses for every supported target. The follow-up verifier
also checks the pool directly against all75 target varieties.
