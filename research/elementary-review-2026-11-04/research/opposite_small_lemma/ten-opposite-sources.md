# Ten diffuse opposite sources suffice

**Status: elementary proof.** Any ten opposite-repeat sources, with
no variety occurring more than twice, assemble an opposite target.

Use the fifteen undirected four-cycles of \(K_5\) for opposite
varieties; every edge denotes both directed corners. The following
counts are elementary:

* an edge belongs to six varieties;
* two distinct edges belong together to exactly two varieties;
* two fixed edges of a target are avoided by exactly five varieties;
* three fixed target edges are avoided by exactly two varieties.

The second count follows by closing a two-edge path through either
remaining vertex, or by choosing one of the two four-cycles through
a pair of disjoint edges. The third follows by inclusion-exclusion,
\(15-6-6+2=5\). For the fourth, the only possible intersection with
the target is its fourth edge, and exactly two varieties have this
one-edge intersection.

If three varieties are doubled, the three-opposite-pairs lemma uses
their six copies and any two further sources. We may therefore
assume at most two varieties are doubled.

If a variety \(P\) is doubled, use \(P\) as target. Each target
edge has its two \(P\) copies. The five varieties avoiding a pair
of target edges do not include \(P\), and at most one of them is
doubled. They account for at most six sources, leaving at least four
neighbours of the pair. At most three sources avoid a triple of target
edges, leaving at least seven neighbours. All four edges meet all ten
sources. These bounds establish Hall for every target-position set.

If all ten sources are distinct, call an edge rare when it belongs
to at most one source. There are five omitted varieties. A rare edge
requires at least five of its six incident varieties to be omitted.
Two rare edges would require at least \(5+5-2=8\) omitted varieties,
which is impossible. Thus there is at most one rare edge.

Choose a target avoiding that edge, if there is one. Each target edge
has at least two source neighbours. A pair of target edges has at
least \(10-5=5\) neighbours, and a triple at least \(10-2=8\).
Hall again gives all eight target positions.

The stronger nine-source theorem is proved separately in
`nine-opposite-sources.md`; this ten-source proof does not depend on
the boundary-case argument there.
