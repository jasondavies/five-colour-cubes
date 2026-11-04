# Four opposite sources: computational reconnaissance

**Status:** discovery and checking, not an elementary proof of exhaustion.

The search uses the twenty directed cuts and fifteen bidirected
four-cycles directly. It considers four opposite sources with variety
cap two, up to colour permutation, and adjacent sources with class
cap three. There are 38 opposite-core orbits. A prefix is discarded
as soon as it already assembles an opposite target; monotonicity
guarantees that none of its extensions can be an opposite failure.

## 1. Four opposite sources plus ten capped adjacent sources

Only one opposite-core orbit has coarse failures:

    2O71 + 2O73,
    O71 = {01,02,14,24},
    O73 = {01,03,12,23}.

Undirected edges denote both corner directions. The two doubled
varieties share edge01. The complement of their union is the path
0–4–3–1, with isolated vertex2.

For this fixed opposite core there are exactly eight failing adjacent
count vectors. All have profile3,3,3,1. They are written in
`opposite-fails-10.jsonl`. All four occupied classes in each vector
share a directed corner.

These are failures of opposite targets only. Their adjacent targets
are soluble, as the earlier conflict-graph calculations already
suggested. This new unrestricted coarse search independently confirms
that the earlier low-cover examples exhaust the opposite failures
under these caps. It is not being used as an elementary exhaustion
argument.

## 2. Much smaller candidate lemmas

The eight-source search of four opposite sources and four adjacent
sources gives the following promising candidates.

> If the four opposite sources have at most one doubled variety,
> four adjacent sources occupying at least three classes always
> assemble an opposite target.

In particular, four distinct adjacent classes suffice in the
at-most-one-double branch. Ten adjacent sources with cap three
occupy at least four classes, so this small statement would settle
that whole branch.

Other observed stronger statements are:

- Four capped opposite sources plus five distinct adjacent classes
  always assemble an opposite target.
- Four capped opposite sources plus eight adjacent sources with
  class cap two always assemble an opposite target.
- Four capped opposite sources plus an adjacent profile3,3,2,2
  always assemble an opposite target.

These assertions are recorded as computational candidates until a
separate hand proof is supplied.

## 3. Four distinct adjacent classes: the only ten failures

With four distinct adjacent classes, every opposite failure uses
the nonneighbouring doubled core2O71+2O73. The ten sets of root-model
class indices are:

    [2,4,9,13], [2,7,13,14], [3,5,8,12], [3,6,12,15],
    [4,7,10,17], [4,9,10,17], [5,6,11,16], [5,8,11,16],
    [6,11,12,15], [7,10,13,14].

They form three geometric families under the stabilizer of the
opposite pair and reversal of every directed corner:

| Shared corner of the four classes | Number of sets | Extension to ten capped adjacent sources |
| --- | ---: | --- |
| 01 or10, the common opposite edge | 2 | None |
| 24,42,23,32 | 4 | One3,3,3,1 extension each |
| 34 or43, the middle edge of the missing path | 4 | One3,3,3,1 extension each |

Thus the eight-source classification, rather than a fourteen-source
inventory classification, may be the useful structural target.

## 4. An elementary closing mechanism for the coarse residuals

A triple class with an own loop must use all three allowed repeated
colours in a failure. If two own-looped triples have intersecting
pole pairs, they cannot coexist in a failure.

Indeed, an own loop for A gives an edge from A to every occupied
class B whose pole pair meets A's: reserve one A and one B instead
of two A. The restored A cube can fill any position lost by removing
a B cube from the six-corner matching. The reserved cubes can supply
the target's two bicoloured corners whenever their repeated colours
agree. Two looped triples have overlapping lists of three repeated
colours on a five-colour palette, giving such an agreement.

For example, one of the coarse residuals is

    O = 2O71+2O73,
    g2=1, g7=g13=g14=3.

The triple classes7 and13 have pole pairs04 and14. After two class7
cubes are reserved, its six tricoloured corners have this matching:

| Corner | Source |
| --- | --- |
| 10 | O73 |
| 14 | O71 |
| 20 | Class14 |
| 24 | Class13 |
| 30 | A second Class14 |
| 34 | The remaining Class7 |

After two class13 cubes are reserved, its six corners have this
matching:

| Corner | Source |
| --- | --- |
| 01 | O71 |
| 04 | Class2 |
| 21 | O73 |
| 24 | Class7 |
| 31 | Class14 |
| 34 | The remaining Class13 |

Thus these two triples are own-looped, and their intersecting poles
give the repeated-colour contradiction. No enumeration of repeated
colour refinements is needed for this residual.

## 5. Search outputs and interpretation

The source is `coarse_search.cpp`. Compile with C++20 and run with
argument10 for the requested total, or4 for the smaller cores.
The respective output files are `opposite-fails-10.jsonl` and
`opposite-fails-4.jsonl`; aggregate statistics are in
`coarse-search-10.txt` and `coarse-search-4.txt`.

At adjacent total4 there are335,730 orbit-representative checks,
of which2,872 fail all opposite targets. The failures by adjacent
profile are:

| Adjacent profile | Number |
| --- | ---: |
| 1,1,1,1 | 10 |
| 2,1,1 | 198 |
| 2,2 | 230 |
| 3,1 | 2,434 |

The first two rows occur only for opposite profile2,2. At adjacent
total10 the only eight failures have profile3,3,3,1.

These counts refer to all labelled adjacent inventories over one
representative of each opposite-core orbit. They are not counts of
physical cube refinements, and should not be quoted as numbers of
full fourteen-cube failures.
