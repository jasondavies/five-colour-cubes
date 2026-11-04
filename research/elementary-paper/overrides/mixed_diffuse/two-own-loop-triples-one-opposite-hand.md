# Two own-loop triples with one opposite source

**Theorem.** A failing pool of fourteen adjacent sources and one opposite
source, with adjacent-class multiplicities at most three, has at most one
triple admitting an own completion. The opposite source may participate
in either asserted completion.

We adapt `research/pure_supported/two-own-loop-triples-hand.md`, retaining
its notation and its explicit final matchings. Only the following changes
are needed; none assumes a completion avoiding the opposite source.

## 1. The two anchors

The repeat-restoration argument in Section 1 of that proof still applies:
restore an anchor copy when removing the other reserved source from an
own completion. It follows that two own-completed triples have disjoint
pole pairs. Normalize them to
\[
A=C(01),\qquad B=C(23)\quad\hbox{or}\quad C=C(014).
\]
The eight other adjacent sources have poles $04,14,24,34$, with forced
repeats $1,0,3,2$, respectively. Denote the opposite source by $O$.

For the disjoint orientation $A,B$, use target $01\mid23$. An adjacent
helper meets one of its directed halves. The source $O$ meets both:
its intersection with $A$ meets at least two of the three columns, hence
meets the rectangle on columns $2,3$; its corners are invariant under
reversal. Put the helper in one half and $O$ in the other, and fill the
remaining three positions in each half with the two anchor triples.

## 2. The nested orientation

For $A,C$, retain the names $P,\bar P,Q,\bar Q,R,\bar R,S,\bar S$
and the main/outer blocks from Section 3 of the pure proof. Put
\[
a=g(\bar P)+g(\bar Q),\qquad b=g(R)+g(S).
\]
Its three restrictions remain valid:

1. $a,b\le3$. Here use Construction III of
   `five-class-mixed-hand-proof.md`: three copies of an adjacent class,
   four sources disjoint from it and one opposite source assemble.
   The first outer block is disjoint from $C$, and the second from $A$.
2. A main class of size three excludes every outer source. The displayed
   repeated-colour constructions in the pure proof use only the anchors,
   that main class and the outer source; they are unchanged.
3. If both main blocks occur, every main count is at most one. Again the
   displayed constructions use only adjacent sources and remain unchanged.

There is an outer source: otherwise eight adjacent helpers would lie in
the main classes. One occupied main block has capacity at most six, while
two occupied blocks have total capacity at most four by restriction 3.
Consequently every main count is at most two. With one main block the
main total is at most four, and with two the same bound follows from
restriction 3. Hence $a+b\ge4$ and both outer blocks occur.

The reverse-square argument from Section 3 of the pure proof now applies
without alteration. If three outer types occur, their at least four
copies fill the reverse square of $01\mid23$, while three $A$ and one
$C$ fill its forward square. Thus the outer classes can be normalized to
\[
\bar P^a,R^b,\qquad 1\le a,b\le3,\qquad a+b\ge4.
\]
There are exactly eight adjacent helpers, so the main total is $8-a-b$.
These are precisely the hypotheses of the pure proof's “remaining
numerical cases.” Its assignments to $04\mid23$ and $13\mid24$ use only
adjacent sources and therefore apply verbatim. Each case assembles,
contradicting failure.

The two alterations from the pure proof are the use of Construction III
to bound the outer blocks, and the capacity argument establishing an
outer source. In particular, neither argument requires the asserted own
completions to avoid $O$.
