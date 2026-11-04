# Seven opposite and seven adjacent sources, with both caps two

**Status: elementary proof.** Seven opposite sources, each variety
occurring at most twice, together with seven adjacent sources, each
tricolour class occurring at most twice, assemble an opposite target.

This settles the entire opposite-total-seven branch of the remaining
fourteen-source problem. The proof uses the three-pairs and
neighbouring-pairs lemmas, and the line-union geometry already written
out in the nine-opposite proof.

## 1. Two rescue edges suffice

For a fixed seven-opposite core, define

\[
E_T=\{c\in T:\text{the seven sources fill }T\setminus\{c\}\},
\qquad E=\bigcup_T E_T.
\]

The sets \(E_T\) are bidirected, since reversing a partial matching
preserves every opposite-source compatibility. Regard \(E\) as a
graph \(B\) of undirected edges on the five colours. Any adjacent
source meeting \(E\) completes a target.

**Rescue observation.** If \(B\) has at least two edges, the seven
adjacent sources force an assembly.

If two edges of \(B\) are adjacent, an adjacent cut avoiding both
must put their three vertices together. Only the two reverse classes
for that three-versus-two partition can avoid them. Their cap allows
at most four adjacent sources, so one of the seven sources meets
\(E\).

If two edges of \(B\) are disjoint, either some adjacent source
meets \(E\), or all seven avoid these two bidirected edges. In the
latter case the endpoints of each edge must stay together on one side
of the cut. The two pairs lie on opposite sides, and the fifth colour
can join either side. There are four possible adjacent classes, two
in each orientation between the pairs. Each orientation has at most
four source copies. The seven sources therefore split as four in one
orientation and three in the other.

Use the opposite target \(K_{2,2}\) between these two colour pairs.
The four sources of the first orientation fill one half. Any opposite
source has a corner in the other half; use it there, and use the three
remaining adjacent sources at the other three positions. This proves
the observation.

We will also use a simple way to obtain two rescue edges from one
target. Suppose the core matches seven positions of \(T\), and the
omitted corner lies on an edge having at least two source neighbours.
One of those source copies is assigned somewhere other than the
reverse corner of that edge. Move that copy to the omitted corner.
Its old position, on another edge, is now omitted. Thus \(E_T\)
contains at least two underlying edges.

Consequently, if \(E_T\) has just one underlying edge, that edge
has source frequency one. In particular, a seven-position matching
to a target represented by two source copies always gives two rescue
edges.

## 2. A five-source completion fact

The five opposite varieties avoiding two fixed undirected edges of
\(K_5\), taken once each, can fill any five positions of an appropriate
opposite target. Here is a direct verification of the only two edge
configurations. The four listed intersections are those of the
noncentral varieties; the central variety sees the entire target.

| Forbidden edges | Five avoiding varieties | Central target | Other four intersections with the target |
|---|---|---|---|
| \(01,02\) | \(60,61,62,63,66\) | \(60=\{13,14,23,24\}\) | \(\{14,23\},\{13,24\},\{23,24\},\{13,14\}\) |
| \(01,23\) | \(62,65,66,69,72\) | \(72=\{02,03,12,13\}\) | \(\{12,13\},\{02,03\},\{03,13\},\{02,12\}\) |

There are exactly five avoiding varieties by inclusion-exclusion:
an edge belongs to six of the fifteen varieties, and two edges belong
together to two, giving \(15-6-6+2=5\). Thus the displayed varieties
are all of them.

Each source sees at least two target edges, and every target edge
belongs to three sources. A two-edge position set has at least four
neighbours, since only the unique variety with the complementary
two-edge intersection can avoid it. A set using three or four target
edges sees all five sources. Hall proves the five-position completion.

Whenever the seven-opposite core contains these five distinct
varieties, the other two opposite sources and any one adjacent source
complete the assembly. The three additional sources match three
distinct target corners: each sees at least two, and their union
cannot have size two because an opposite-source intersection is
bidirected while an adjacent-source intersection uses distinct
underlying edges. The five-source core fills the remaining positions.

## 3. No doubled variety, or exactly one

First suppose all seven opposite varieties are distinct. If the
five-variety configuration of §2 occurs, we are done. Otherwise every
target represented among the seven sources has a seven-position
matching. Indeed source-side Hall can fail only when three sources
are confined to one target edge, or five sources are confined to two,
or all seven are confined to three. The first is impossible with
distinct varieties, since exactly two varieties have a given single-edge
target intersection. The second would give the five varieties of §2.
The third is impossible because the target's own source sees all
four edges.

If the global rescue graph had at most one edge, the seven represented
targets, each with a nonempty rescue set, would all contain that same
edge. But an edge belongs to only six opposite varieties. Thus there
are at least two rescue edges, and §1 applies.

Next suppose \(P\) is the sole doubled variety. Use target \(P\).
If it has a seven-position matching, its two own copies give at least
two neighbours on every edge, so §1 again applies.

If not, the obstruction cannot include a \(P\) copy, since such a
copy sees all eight positions. Among the other five single sources,
at most two can be confined to one edge. The only possible source-side
Hall failure therefore confines all five to two target edges. They
are precisely the five varieties avoiding the complementary two
edges, and §2 applies.

## 4. Two or more doubled varieties

Three doubled varieties are handled by the three-pairs lemma, using
the seventh opposite source and any adjacent source as the two extras.
Two doubled neighbouring varieties are handled similarly by the
neighbouring-pairs lemma.

It remains to consider

\[
2P+2Q+R+S+U,
\]

where \(P,Q\) share exactly one edge \(e\), and the other three
varieties are distinct. If either \(P\) or \(Q\), used as target,
has a seven-position matching, its two own copies give two rescue
edges. We may suppose both targets have matching rank at most six.

There is a unique third variety \(V\) that intersects each of
\(P,Q\) only in \(e\). For a direct normal form, write

\[
P=60=\{13,14,23,24\},\quad
Q=67=\{01,04,13,34\},\quad
V=72=\{02,03,12,13\}.
\]

Any two four-cycles on five vertices sharing exactly one edge have
this form after relabelling: their three shared vertices include the
common edge, and their paths around their respective fourth vertices
must attach the third shared vertex to opposite endpoints of that
edge. The third cycle displayed is then the unique one-edge
intersection companion for both.

### The companion V is absent

Consider source-side Hall for a seven-position matching to \(P\).
An obstruction cannot include a \(P\) copy. Three sources could be
confined to one edge only if they were the two \(Q\) copies and
the companion \(V\), which is absent. Thus the only remaining
obstruction confines all other five sources to two target edges.
Those two edges include \(e\), since they contain \(Q\)'s
intersection with \(P\).

Consequently all three single varieties avoid a two-edge set
\(F\subset P\setminus Q\). Applying the same argument to target
\(Q\), all three avoid a two-edge set
\(G\subset Q\setminus P\). The sets \(F,G\) are disjoint.

The six-edge graph \(L=K_5\setminus(F\cup G)\) contains the
three distinct single varieties. As proved explicitly in
`nine-opposite-sources.md`, it is a line union \(K_4\) or
\(K_{2,3}\). The varieties \(P,Q\), whose outside pairs partition
the complement of \(L\), have a common high target \(T\) in this
line. The same note gives normal forms for both cases.

All seven sources meet \(T\) in at least two edges, and the three
single line varieties supply at least two neighbours on every edge.
They fill any seven target positions by the robust-seven Hall argument
in that note. Any adjacent source supplies the eighth position.

### The companion V is present

Use the displayed normal form, so the core is \(2P+2Q+V+S+U\).
Consider two targets

\[
T_1=62=\{12,13,24,34\},\qquad
T_2=66=\{03,04,13,14\}.
\]

On each target, the patterns of \(P,Q,V\) have a common edge
\(13\) and three different private edges. Explicitly:

| Target | \(P\)-intersection | \(Q\)-intersection | \(V\)-intersection |
|---|---|---|---|
| \(T_1\) | \(13,24\) | \(13,34\) | \(13,12\) |
| \(T_2\) | \(13,14\) | \(13,04\) | \(13,03\) |

Each target has a seven-position matching. For source-side Hall, at
most the two additional single sources \(S,U\) can be confined to
one edge. A two-edge set can contain at most one of the three displayed
patterns, hence at most two displayed source copies and the two
additional sources: four in total. All seven cannot be confined to
three edges, since the displayed patterns jointly use all four.

All edges of \(T_1\) have source frequency at least two except
possibly \(12\); all edges of \(T_2\) have frequency at least two
except possibly \(03\). By the exchange observation in §1, if
\(E_{T_1}\) has just one underlying edge it must be \(12\), and
if \(E_{T_2}\) has just one it must be \(03\). Since both rescue
sets are nonempty, their union contains at least two different edges.
The seven adjacent sources now force a solution by §1.

This exhausts the opposite multiplicity profiles and proves the
fourteen-source theorem.

## Remaining gap

Together with the nine-opposite theorem and the eight-opposite rescue
lemma, the unresolved capped mixed branch is now confined to

\[
o\in\{5,6\},\qquad g_j\le2,\qquad n_O\le2.
\]

No elementary exclusion of these two remaining totals is claimed here.
