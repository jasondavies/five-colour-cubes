# Four distinct opposite sources and ten capped adjacent sources

**Status: elementary proof.** The full argument has passed independent
root audit.

**Theorem.** Four pairwise distinct opposite-repeat sources, together
with ten adjacent sources whose tricoloured-corner class counts are
at most three, contain an opposite-target assembly.

The argument uses rank-two hole geometry on the six-corner grid of a
repeated adjacent class. It reduces to the same two central-target
geometries used in the earlier five-opposite argument, but its
classification is different because there are only four opposite
sources.

## 1. Two elementary facts about adjacent cuts on an opposite target

Fix an opposite target T. Every adjacent class meets T in two or four
directed positions, on two or four underlying edges respectively.
It never contains both directions of an edge.

At most two adjacent classes have their T-intersection inside any
specified two-position set. A two-position pattern is either a star,
which determines the class uniquely, or two opposite edges, with the
fifth colour free to join either side, which gives two classes.

At most three adjacent classes have their T-intersection inside a
specified three-position set. To see this, no four-position pattern
fits there. If two positions are the reverse directions of an edge,
the only possible two-position patterns pair the third position with
one of them, giving at most two classes. Otherwise the three positions
lie on a three-edge path in the target four-cycle. The two end edges
can give one opposite-edge pattern, with two classes. When that pattern
is valid, the middle position forms a valid directed star with at most
one end, adding at most one class. If the end-edge pattern is invalid,
only the two possible stars remain. The bound is three in all cases.

In particular, ten adjacent sources with class cap three cannot all
have their target intersections inside three positions.

## 2. A four-source central-target completion lemma

Suppose four distinct opposite sources have these properties on an opposite
target T:

1. Every source meets at least two underlying target edges.
2. Every target edge has at least two source neighbours.

They fill every four-position set whose positions use at least three
underlying edges. Indeed, any one-edge subset has at least two
neighbours. A two-edge subset has at least three neighbours: only the
unique opposite variety whose target intersection is the complementary
two-edge pair can avoid it, and the present four sources are distinct.
A subset using at least three edges meets all four sources. Hall
therefore proves the claim whenever no four-position subset consists
of two complete bidirected edges.

Now suppose two of the ten actual adjacent sources are in a class A
with A∩T={a,b}. Reserve these two copies at a,b, on distinct edges.
Let F be the pair of underlying edges of a,b.

If an adjacent source has a corner c on an edge outside F, two
distinct adjacent helpers can match distinct unreserved corners, at
least one of which lies outside F. Here is the small matching argument.
After the two A copies are removed, at least four of the eight helpers
have a corner outside {a,b}: at most two classes, hence at most six
total copies, can be confined to {a,b}. Choose a helper at such a c.
If another helper has an unreserved corner d≠c, use those two.
Otherwise every other nonempty helper is confined to c outside {a,b}.
If the first helper has another unreserved corner d, put it at d and
another helper at c. If it does not, all ten source intersections lie
in {a,b,c}, contradicting the three-position bound of Section 1.

Together with a,b, the two helper positions use at least three target
edges. Their four-position complement also uses at least three edges,
so the four opposite sources fill it by the preceding Hall argument.

It remains that all ten adjacent sources have their target
intersections contained in the two bidirected edges F. If the edges
meet, there are only two possible directed-star classes, with total
capacity six, impossible. If the edges are disjoint, exactly four
classes are possible: two classes with each of two opposite
orientations, according to the side chosen by the fifth colour.
Each orientation has capacity six, so both have at least four actual
sources. The four classes share another high opposite target: use the
two-versus-two partition that their directions prescribe on the four
vertices of T. Four sources in each orientation fill its two directed
halves. Thus eight adjacent sources alone assemble.

Consequently the hypotheses of this central-target lemma always give
an assembly of the full fourteen-source pool.

## 3. The high-rectangle replacement step

If the ten adjacent sources occupy at least nine classes, use the
previous nine-distinct-class theorem. Otherwise choose a class A
occurring at least twice and normalize its grid to

    02 03 04
    12 13 14.

Every opposite variety meets this grid in either two positions in
different columns or a complete two-column rectangle. Its pattern
determines its variety uniquely.

If the four opposite sources match a complete two-column rectangle,
they and four hypothetical A copies assemble the corresponding
opposite target, using four A in one directed half and the four
opposite sources in the other. Replace two hypothetical A copies by
any two actual adjacent helpers. Each helper meets at least two
underlying target edges, so choose distinct edges for them. If a
helper's direction is reversed, interchange its position with the
opposite source on the same edge. These independent exchanges leave
two actual A copies and the two helpers in a valid assembly.

Thus we may assume all three high rectangles have matching rank at
most three.

## 4. The rank-two classification of four distinct grid patterns

The four opposite sources have matching rank four on the full grid.
Indeed every pattern has at least two positions; three distinct
patterns cannot be confined to two positions; and four distinct
patterns cannot be confined to three positions, since at most three
varieties have patterns inside three positions. Source-side Hall
therefore gives rank four.

Take the rank-four transversal matroid M on the six grid positions,
and its rank-two dual N. A pair of positions is a basis of N exactly
when the four sources match its four-position complement. Each
same-column pair is therefore a nonbasis, by the high-rectangle
assumption. Let H be the nonloop set of N, the positions that can
occur in a pair of holes.

Alternating paths from the two holes of a matching show that

    |N_O(H)| = |H|−2.

Every source adjacent to H is matched inside H and exactly two
positions of H are unmatched. Sources outside this neighbourhood
avoid H entirely.

If |H|=4, two opposite sources would have their entire grid patterns
inside the other two positions, forcing the same variety twice.
If |H|=5, one source would have its entire pattern in one position.
Both are impossible here.

Suppose |H|=6. Every column's two positions are then parallel in the
rank-two matroid N. Its parallel classes are either the three
separate columns, or one class consisting of two columns and one
consisting of the third.

In the three-class case, any two positions in different columns form
a basis of N. No opposite source can have a two-position grid pattern:
deleting that pattern would leave a four-position M basis with no
available corner for that source. All four sources would therefore
have to be high-rectangle varieties, but there are only three of those.

In the two-class case, let V be the single-column parallel class,
and U the other two columns. Dual rank gives r_M(V)=1. There are no
M loops: a loop would be a coloop of N, which is impossible in a
rank-two matroid all of whose parallel classes have size at least
two. Both positions of V are therefore supported, and r_M(V)=1
forces exactly one opposite source R to meet V, containing both
positions. Its grid pattern is a rectangle on V and one column of U.
The three other distinct sources have their patterns entirely in U.
All four source restrictions to U have at least two positions. Three
of them cannot be confined to a two-position set: R's restriction is
a column, whereas the other two-position patterns use different
columns and are distinct. Their total union is all four positions
of U, since M has no loops. Hall gives a matching of U, contradicting
the high-rectangle assumption.

It follows that |H| is two or three.

### Two hole positions

No opposite source meets H. All four patterns lie inside the other
four positions. The holes belong to different columns, because they
form a basis of N. Thus the containing four-position shape has
column sizes 2,1,1.

### Three hole positions

Exactly one source meets H. The other three distinct sources lie in
its three-position complement. Those three positions must occupy
three different columns; a shape in only two columns supports just
two varieties. The three sources are therefore precisely the three
two-position patterns on one position per column. They form a line
of opposite varieties, and the fourth source is outside the line.

These are the only two geometric alternatives.

## 5. Both alternatives give a central target

For the four-position shape of column sizes 2,1,1, take the target T
determined by the two singleton-column positions. The five possible
opposite varieties supported on that shape each meet T in at least
two edges, and every target edge belongs to three of the five
varieties. These are the two explicit diagrams in Section 3 of
`../opposite_small_lemma/six-opposites-three-adjacent.md`.
Our four distinct sources omit only one of those five types. Hence
every target edge still has at least two source neighbours.

For the three-position line, let S be the fourth source and take its
unique high target T in the line. The other two line varieties each
meet T in two edges, and S also meets T in two. Every edge of T is
seen by T itself and one of the other line varieties. Again every
edge has at least two neighbours.

In both alternatives A meets T in exactly the two positions defining
the central pattern. Thus all hypotheses of Section 2 hold, and an
assembly follows. This proves the theorem.

## Scope

This completes the opposite profile 1,1,1,1 for the requested target.
The analogous rank-two analysis for profile 2,1,1 can additionally
have four nonloop hole positions, and its central targets may have
edges of opposite frequency one. Those issues are not claimed to be
settled by this note.
