# Six opposite and eight adjacent sources, with both caps two

**Status: elementary proof.** Six opposite sources, each variety
occurring at most twice, together with eight adjacent sources, each
tricolour class occurring at most twice, assemble an opposite target.

The proof uses Hall's theorem, elementary rank-two matroid facts, the
eight-opposite theorem in `../root/eight-opposite-elementary.md`, and
the established three-pairs and neighbouring-pairs constructions.
The only final configuration table has two rows, both with explicit
corner assignments.

Throughout, an undirected edge denotes its two directed tricoloured
corners. Write \(C(S)\) for the adjacent cut \(S\to S^c\), where
\(|S|=2\) or \(3\).

## 1. Preliminary reductions

Assume for contradiction that the fourteen-source pool has no opposite
assembly. Three doubled opposite varieties would give the three-pairs
construction. Two doubled neighbouring opposite varieties would give
the neighbouring-pairs construction using all six opposite sources and
any two adjacent sources. These cases are therefore excluded.

Let \(Z_O\) be the set of undirected edges absent from all six
opposite sources. Let \(Z_A\) be the set of edges for which neither
orientation occurs in any of the eight adjacent sources.

### At most one opposite-zero edge

If two edges are in \(Z_O\), all six opposite sources belong to the
five varieties avoiding those edges. The two diagrams in §2 of
`seven-opposites-seven-adjacent.md` give a central target for these
five types. Every type sees at least two target edges, and each target
edge is missed by only two of the five types. Under multiplicity cap
two, at most four sources miss any one target edge. Thus every edge
has at least two neighbours. A pair of target edges has at least four
neighbours, because only the unique variety with the complementary
two-edge intersection can avoid it. Three target edges meet all six
sources. The six sources consequently fill any six target positions.
Two arbitrary adjacent sources choose distinct compatible corners,
and the core fills the rest. Hence

\[
|Z_O|\le1.
\]

### At most one adjacent-zero edge

Adjacent cuts avoiding two adjacent bidirected edges must put their
three vertices on one side. Only two reverse classes do so, allowing
at most four copies under the class cap. Thus even seven adjacent
sources cannot all avoid those two edges.

For two disjoint edges, a cut avoiding both must keep each endpoint
pair together. The pairs occupy opposite sides, and the fifth colour
joins either side. There are four classes, two in each orientation
between the pairs. Seven adjacent sources avoiding the two edges
split as four and three between these orientations, since each
orientation has capacity four. The four sources fill one half of the
opposite target between the pairs; any opposite source and the other
three adjacent sources fill the other half.

Consequently, in the assumed failure, **no seven adjacent sources
avoid two undirected edges**. In particular,

\[
|Z_A|\le1.
\]

### A seven-opposite rescue property

For any seven-opposite core with cap two, let its rescue graph consist
of the edges whose directed corners can be left as the sole hole in
a seven-position matching to some opposite target. This graph meets
every adjacent cut. One way to see this uses the eight-opposite theorem.
Fix an adjacent class \(A\). Its three two-column rectangles give
three opposite varieties whose corners lie in \(A\cup\overline A\).
If all three are already doubled, the three-pairs lemma uses those
six sources, the seventh opposite source, and \(A\). Otherwise add
one of these varieties that is not doubled. The eight-opposite theorem
gives an assembly. Its added source supplies a corner of \(A\) or
\(\overline A\). In the latter case reverse all corner directions;
every opposite source and the target are bidirected. Replace the added
source by \(A\).

In particular, a seven-opposite rescue graph cannot have at most one
edge. We will also use the stronger statement just established: it
cannot be a proper subgraph of a three-edge path on four vertices,
since a proper subgraph of that path admits a two-versus-three cut
avoiding all its edges.

## 2. The two-hole structure of a six-opposite core

Fix a target \(T\) on which all six opposite source copies can be
matched. A pair of target corners is **admissible** if deleting the
pair leaves six positions that the core can fill.

The matchable target-position sets form a rank-six transversal matroid.
Their six-position bases have two-position complements, which are the
bases of its rank-two dual. The elementary rank-two description is:
some positions never belong to an admissible pair; the remaining
positions split into parallel classes, and a pair is admissible exactly
when its two positions belong to different classes.

Let \(H\) be the set of positions appearing in admissible pairs.
We record three facts about this description.

### 2.1 Bidirectionality

Swapping the two orientations of any target edge preserves every
opposite-source compatibility and therefore every admissible pair.
Thus \(H\) is a union of complete bidirected edges. A parallel class
with more than one position is also a union of complete bidirected
edges. If the two positions of one edge lie in different classes,
both classes are singletons: swapping those two positions fixes all
other positions, so neither can be parallel to any other position.

### 2.2 Exactly |H|−2 opposite copies meet H

Choose a matching of the six sources, leaving two target positions
unmatched. Start alternating paths at those two unmatched positions.
The positions reachable by such paths are precisely \(H\): exchanging
along a path makes its endpoint a hole, and the symmetric difference
with any other matching gives the converse.

Every source copy adjacent to \(H\) is matched to a position in
\(H\), since otherwise the alternating path would reach a position
outside \(H\). Conversely each matched position of \(H\) has
such a source. Exactly two positions of \(H\) are unmatched, so

\[
|N_O(H)|=|H|-2.
\]

The source copies outside \(N_O(H)\) avoid \(H\) and occupy the
other target positions. Thus the rank-two hole matroid on \(H\) is
the dual of the transversal matroid obtained by matching just the
\(|H|-2\) source copies of \(N_O(H)\) to \(H\).

### 2.3 Adding a virtual opposite source

Add an opposite source \(R\) whose variety is not already doubled.
A corner \(c\) is a sole rescue hole of the resulting seven-source
core on \(T\) exactly when there is a corner \(d\) of \(R\) in
\(H\) such that \(c,d\) lie in different parallel classes.
Indeed the original six sources fill the complement of \(c,d\),
and \(R\) fills \(d\). Conversely every seven-position matching
uses all six original sources and \(R\), giving such a pair.

Targets on which the original core has rank below six contribute
no seven-source rescue corners.

## 3. What failure forces on each two-hole matroid

If \(H\) consists of just one bidirected edge, §2.2 shows that no
opposite source contains that edge. It therefore belongs to \(Z_O\).

Suppose \(H\) contains at least two edges. At least two adjacent
source copies meet \(H\); otherwise seven adjacent sources would
avoid two of its edges, contradicting §1.

If the adjacent sources collectively meet two parallel classes in
\(H\), two distinct adjacent sources can occupy an admissible pair.
To check this, take any two copies meeting \(H\). If their available
positions do not permit different classes, both are confined to one
class; any source with a position in another class can then be paired
with either of them. Thus failure forces **all adjacent-source corners
in \(H\) to lie in one parallel class \(D\)**.

There are only two possibilities.

### Type I: D is bidirected

The nonempty complement \(H\setminus D\) is bidirected and is
avoided by every adjacent source. Since \(|Z_A|\le1\), it consists
of a single edge \(f\in Z_A\).

This edge has opposite-source frequency exactly one. To see this,
write \(h=|H|\) and let \(M\) be the transversal matroid on
\(H\) from §2.2, of rank \(h-2\). Its dual \(N\) has rank two.
The parallel class \(D\) has dual rank one and size \(h-2\).
The dual rank identity gives

\[
1=r_N(D)=|D|-r_M(H)+r_M(H\setminus D)=r_M(\{f,\bar f\}).
\]

Opposite sources see both orientations of an edge, so this last rank
is one precisely when exactly one source copy contains \(f\).

If a virtual opposite source \(R\) avoids \(f\), its \(H\)
corners lie in \(D\). By §2.3, every rescue corner it creates on
this target lies on \(f\).

### Type II: D is a singleton

Let its corner lie on edge \(e\). Its reverse is a separate
singleton class. All other edges of \(H\) are avoided by every
adjacent source. There can be only one such other edge, denoted
\(f\in Z_A\). Thus \(H\) consists of the four positions on
\(e,f\).

Exactly two opposite source copies meet \(H\), by §2.2. The two
positions of \(e\) form an admissible pair, so those two source
copies can fill both positions of \(f\). Hence \(f\) has opposite
frequency two. Every opposite source containing \(e\) is among
these same two copies. All adjacent sources avoid \(f\), and on
\(e\) they use only the one orientation in \(D\).

These are the complete possibilities for a rank-six target in the
assumed fourteen-source failure.

## 4. A virtual seventh source removes most possibilities

If \(Z_A\) is empty, no target can have \(|H|\ge4\), by §3.
Choose an opposite variety \(R\) avoiding the possible one edge
of \(Z_O\), and not already doubled. Adding it creates no rescue
corner on any target, by §2.3. This contradicts the seven-opposite
rescue property.

Now suppose \(Z_A=\{f\}\). If the opposite frequency of \(f\)
is zero or at least three, neither Type I nor Type II is possible.
The same argument applies.

If its opposite frequency is one, only Type I is possible when
\(|H|\ge4\). Choose \(R\) avoiding \(f\) and the possible edge
of \(Z_O\). This is possible with the cap maintained: at least five
varieties avoid any pair of edges, while at most three varieties can
be doubled among six source copies. After adding \(R\), one-edge
sets \(H\) create no rescue corners, and every larger \(H\)
creates rescue corners only on \(f\). The entire rescue graph has
at most one edge, again a contradiction.

It remains that \(f\) has opposite frequency two. Larger sets
\(H\) are then all Type II. Their nonloop edge sets are \(\{e,f\}\),
and every source containing \(e\) is one of the two copies
containing \(f\).

Consider the other four opposite copies, which avoid \(f\). If
one of their varieties is single, add a second copy of that variety
as \(R\). This source avoids every Type-II set \(H\): it avoids
\(f\), and cannot contain an edge \(e\) whose source neighbours
are confined to the two \(f\)-containing copies. It also avoids
every edge of \(Z_O\), since it is a copy of an existing source.
No target supplies a rescue corner, contradicting the seven-opposite
rescue property.

Therefore the four copies avoiding \(f\) must be two doubled
varieties \(P,Q\). The two copies containing \(f\) are distinct
single varieties \(S,U\), since otherwise there would be three
doubled varieties. The varieties \(P,Q\) are nonneighbouring by §1.

## 5. The final path configuration

Normalize

\[
P=60=\{13,14,23,24\},\qquad
Q=67=\{01,04,13,34\}.
\]

Their union contains seven edges. Its complement is the three-edge
path

\[
K=\{03,02,12\},\qquad 3-0-2-1.
\]

The adjacent-zero edge \(f\) belongs to \(K\), since \(P,Q\)
avoid it. Every Type-II nonloop edge \(e\) also belongs to \(K\),
because only \(S,U\) can contain it. Any opposite-zero edge lies
in \(K\) as well. Consequently **every rank-six target has all its
nonloop hole positions on edges of \(K\)**.

Add a second \(S\) copy. By §2.3 its seven-source rescue graph is
a subgraph of \(K\). It must meet every adjacent cut, by §1.
Every proper subgraph of a three-edge path on four vertices admits
a two-versus-three cut avoiding it: keep each of its connected
components together. Thus the rescue graph is all of \(K\).

For either edge \(g\in K\setminus\{f\}\), this rescue cannot
come from a one-edge set \(H=\{g,\bar g\}\). Such an edge is
opposite-zero, and the added \(S\), being a copy of an existing
opposite source, avoids it. Therefore it comes from a Type-II set
with edges \(g,f\). All eight adjacent sources consequently avoid
one orientation of \(g\).

We have proved that the eight adjacent sources avoid both directions
of one path edge \(f\), and one direction of each of the other two
path edges. The next short enumeration is of cuts of this single
four-vertex path, not of cube inventories.

### 5.1 The allowed adjacent classes

Reversing the path exchanges \(P,Q\), so \(f\) is either the end
edge \(03\) or the middle edge \(02\). Reversing all directed
corners also preserves all opposite varieties and assemblies.

If \(f=03\), regard \(0,3\) as one block of size two. The other
path vertices are 2 and 1. When the two forbidden directed edges
form a directed chain on these three blocks, only three balanced
cuts are possible. When they both point into vertex 2, or both out
of it, four cuts are possible. Up to global reversal, the four-cut
case forbids \(02\) and \(12\), and its source sides are

\[
124,\quad12,\quad023,\quad24.
\]

For completeness, if the block \(03\) is on the source side,
avoiding \(02\) forces 2 onto that side, giving \(023\).
If the block is on the other side, the source side is a two- or
three-element subset of \(124\); avoiding \(12\) leaves
\(12,24,124\). Reversing one of the two forbidden directions
instead leaves only three cuts.

If \(f=02\), contract \(0,2\) to a block of size two. The other
path vertices are 3 and 1. A directed chain through the size-two block
leaves only two balanced cuts. Restrictions both pointing away from
the size-two block, or both towards it, leave four. Up to reversal,
forbid \(03\) and \(21\). The size-two
block cannot be on the source side, since that would force both
1 and 3 onto the source side as well. The allowed source sides are
therefore

\[
134,\quad13,\quad14,\quad34.
\]

Eight adjacent sources with cap two cannot occupy only two or three
classes. Hence one of these four-class configurations occurs, and
each listed class occurs exactly twice.

### 5.2 Explicit assemblies

Both configurations assemble target \(P=60\) using its two source
copies and six adjacent sources. The entries below specify the
adjacent assignments; the two \(P\) copies fill the listed remaining
positions.

| Zero path edge | Adjacent-source assignments | Remaining corners for two P copies |
|---|---|---|
| \(03\) | Two \(C(124)\) at \(13,23\); two \(C(12)\) at \(14,24\); one \(C(023)\) at \(31\); one \(C(24)\) at \(41\) | \(32,42\) |
| \(02\) | Two \(C(134)\) at \(32,42\); one \(C(13)\) at \(14\); one \(C(14)\) at \(13\); two \(C(34)\) at \(31,41\) | \(23,24\) |

Every assignment is an edge of the indicated directed cut, and all
eight target positions are distinct. Global reversal gives the other
orientations. This final contradiction proves the theorem.

## Remaining capped mixed gap

The opposite totals six, seven, and at least eight now have elementary
proofs. After the already established adjacent-class reductions,
the only unresolved large-opposite case is

\[
o=5,\qquad g_j\le2,\qquad n_O\le2.
\]

No proof of that last case is claimed in this note.
