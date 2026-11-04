# Five opposites and nine capped adjacent sources: two doubled opposites

**Theorem.** A pool consisting of five opposite sources of profile
`2,2,1`, and nine adjacent sources with each tricoloured-corner class
occurring at most twice, assembles an opposite target.

This is an elementary consequence of the existing grid proofs and the
replacement lemma below. No inventory enumeration is used.

## 1. Replacing the third copy of an adjacent class

**Replacement lemma.** If five opposite sources together with three
copies of an adjacent class A assemble an opposite target, then the
same five opposite sources together with two A sources and any other
adjacent source B also assemble an opposite target. B may equal A.

In the given assembly, the three A corners lie on three distinct
undirected target edges. An adjacent source meets an opposite target
on at least two distinct underlying edges. Thus B meets the edge of
one of the A corners. If B supplies the assigned direction, replace
that A directly. Otherwise interchange the two directions of that
edge throughout the assignment, then replace A by B. The reverse
position was assigned to an opposite source, since A never contains
both orientations of one edge. Every opposite source remains compatible
after this interchange. The other two A assignments are unaffected.

## 2. Choose a doubled adjacent class

If the nine adjacent sources belong to nine distinct classes, they
already assemble by `../root/nine-distinct-hall-proof.md`. Otherwise
choose a class A represented twice; such a class is available because
the class cap is two. Normalize A=C(01).

Write the opposite sources as 2P+2Q+R, with P,Q,R distinct. If P and Q
share two undirected edges, `../opposite_small_lemma/five-opposites-neighbouring-pairs.md`
assembles 2P+2Q+R+2A+B for any occupied class B different from A.
Such a B exists because only two of the nine adjacent sources are A.

Suppose P,Q share only one undirected edge. Temporarily consider the
eight-source pool 2P+2Q+R+3A. If it assembles, the replacement lemma
gives an assembly using two actual A sources and any third actual
adjacent source.

We may therefore assume that temporary pool fails. Its three
two-column grid rectangles all have opposite matching rank at most
three: a rank-four rectangle would have four reverse corners filled
by four opposite sources, while the unused opposite source and 3A
fill the forward rectangle.

The Hall cover argument in Section 1 of
`../opposite_small_lemma/five-opposites-nonneighbouring-pairs.md`
therefore applies without change. It leaves one overlapping grid
form and three disjoint forms. This reduction depends only on the
five opposite sources and A, not on the presence of three actual A
sources in the fourteen-pool.

## 3. The existing final constructions use only two A sources

For the overlapping form, that note gives two possible targets. Each
uses exactly two A sources and all five opposite sources; any further
adjacent source meeting a specified rescue set completes it. At most
two adjacent classes avoid the rescue set.

For every disjoint form, the same note gives two complementary
constructions. Their combined rescue set consists of two bidirected
edges and one directed edge joining their components. At most two
adjacent classes avoid that set. Each construction again uses exactly
two A sources, all five opposite sources, and one rescuing adjacent
source.

With class cap two, at most four of the nine actual adjacent sources
can avoid any of these rescue sets. Both selected A copies avoid the
set in the construction, so a source meeting it is automatically
distinct from those copies. Thus an actual rescue source exists and
the assembly follows.

## Audit of the adaptation

The only use of a third A source in the cited nonneighbouring-pairs
proof is the initial rank-four rectangle construction. Here that use
is justified by the replacement lemma. The overlapping and all three
disjoint final constructions reserve only two A sources. Their
existence-of-rescue argument used nine adjacent sources with class cap
three; the present class cap two gives the stronger bound of at most
four avoiding sources. No virtual cube is used in the final assembly.

The same replacement argument can be applied to the low-repetition
grid proof to treat the other opposite profiles; that extension is
handled by the root proof.
