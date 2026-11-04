#!/usr/bin/env python3
"""Reproducible, bounded editorial pass. Original research notes are untouched.

These transformations share proved arguments; they do not certify their proofs.
Each removed mathematical passage is either unused by the threshold route or
replaced with an explicit statement of the argument retained elsewhere.
"""
from pathlib import Path
import re

BASE=Path(__file__).resolve().parents[1]
SRC=BASE.parent/'elementary-review-2026-11-04/research'

def read(name): return (SRC/name).read_text()
def save(name,s):
 p=BASE/'overrides'/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
def replace(s,a,b):
 assert a in s,a
 return s.replace(a,b)

# Stronger row/diagonal proofs already needed in the one-opposite branch
# subsume the earlier conditional versions. Copy the shared geometric steps
# into those proofs before removing their references to the earlier versions.
f='root/g3-private-column-hand.md';s=read(f)
s=replace(s,'The last fact is proved in\n`g3-private-row-hand.md` and `g3-private-diagonal-hand.md`, using\n`../pure_supported/g3-nonprivate-hand.md`.',
 'The stronger private-column lemma in\n`../pure_supported/private-diagonal-unconditional-hand.md` proves this\nwithout assuming that the other triples lack own completions.')
save(f,s)

f='pure_supported/private-diagonal-unconditional-hand.md';s=read(f)
a=s.index('A matching of four outsiders');b=s.index('It follows that `z<=3`.',a)
s=s[:a]+r'''A matching of four outsiders to any reverse rectangle
`q0,q1,s0,s1` implies an opposite assembly. To verify Hall, a set of at
most three target corners meeting A has its three copies as neighbours.
A four-set meeting A gains an outsider from the reverse matching if it
meets the reverse half; otherwise A has only two private corners, so
the forward four-set also gains an outsider. Reverse-only sets are
covered by the assumed matching. For five- and six-sets, their complements
contain complete intersections of at most three and two adjacent classes,
respectively. The class cap gives at least $14-9=5$ and $14-6=8$
neighbours. A complement of at most one corner contains no whole source
intersection. These are all Hall inequalities.

'''+s[b:]
s=re.sub(r'This corrects the error in the\nfirst draft of this note\.','',s)
save(f,s)

f='pure_supported/private-row-unconditional-hand.md';s=read(f)
a=s.index('This removes the all-private');b=s.index('## 1.',a)
s=s[:a]+'''The dependencies are the nonprivate-triple lemma
`g3-nonprivate-hand.md`, the two-own-loop exclusion
`two-own-loop-triples-hand.md`, the six-repeated-class bound
`../root/six-doubled-classes-hand.md`, and the common-corner lemmas
cited below. None uses this row-pair exclusion.

'''+s[b:]
# The old row proof has the full geometric reduction, ending exactly where
# it first uses the extra all-private hypothesis. Retain that prefix alone.
old=read('root/g3-private-row-hand.md')
a=old.index('## 1.');b=old.index('Both contradict the private-corner hypothesis.')
geom=old[a:b]
geom=geom.replace('## 1. The eleven possible outsider classes','## 1. Row geometry')
geom=geom.replace('## 2. At most three zero-intersection sources','### At most three zero-intersection sources')
geom=geom.replace('## 3. Two sources meeting the reverse 1-column force a solution','### Reducing to two exceptional supports')
a=s.index('## 1.');b=s.index('## 2.',a)
s=s[:a]+geom+'\n'+s[b:]
a=s.index('This is the elementary\ntwo-absence check');b=s.index('Hence at most one triple',a)
s=s[:a]+'''Here is the two-absence check. In the common-corner family,
P_i has private arcs $i\to j,i\to k$ only when $N_j,N_k$ are
absent; if only $N_j$ is absent, a second private arc $1\to j$
also requires $P_k$ absent. The dual statements hold for N_i.
The additional class A supplies every $1\to q$, removing that
second P-type arc. If both absent classes are N-types, only the
complementary P-type can retain two private corners; the dual holds
when both are P-types. With one absent type of each kind, at most
one N-type retains two. '''+s[b:]
# Python literal backslash-t above must be genuine LaTeX, not tabs.
s=s.replace('\t'+'o',r'\to')
save(f,s)

# Restore the previously dropped extension lemma while excluding its separate
# 91-refinement calculation. Keep the butterfly necessity used to add an
# opposite source; its converse and the enumeration are not needed here.
f='invariant_structure/elementary_refinements.md';s=read(f)
a=s.index('## 2.');b=s.index('### A useful extension lemma',a)
s=s[:a]+r'''## 2. A concentrated-opposite extension

Write $O=O(0;12\mid34)$, $A=C(01)$, and $B=C(124)$.

'''+s[b:]
a=s.index('For sufficiency,');b=s.index('## 4.',a)
s=s[:a]+s[b:]
s=s.replace('The collection fails if and only if both low cubes repeat z,',
 'If the collection fails, both low cubes repeat z,')
a=s.index('A failing collection with three identical opposite cubes must')
b=s.index('## 7.',a)
s=s[:a]+'''Thus a failing collection with three identical opposite cubes
must have a size-four Hall cover. The arguments above do not use the
subsequent analysis of those four-corner covers.

'''+s[b:]
save(f,s)

f='root/o4-elementary.md';s=read(f)
s=s[:s.index('This proves the theorem.')]+'This proves the coarse-profile theorem.\n'
save(f,s)
f='root/o3-butterfly.md';s=read(f)
s=s[:s.index('In the latter form, U must use')]+'''Hence every surviving coarse profile is three identical opposite
copies and adjacent-class sizes $5,3,3$. Only this necessary profile
is used in the threshold proof.
'''
save(f,s)
f='root/o3-covers-guide.md';s=read(f)
a=s.index('Only the first cover family');b=s.index('The arguments for covers53',a)
s=s[:a]+'''Only the first cover family can survive; its analysis forces
three identical opposite copies and adjacent-class sizes $5,3,3$.
Together with the four-copy theorem, this proves the necessary coarse
profiles for failures with an opposite multiplicity at least three.

'''+s[b:]
save(f,s)

# The butterfly profile is only used after pure concentration has given cap
# three. Its stronger cap-five proof and the unrelated common-corner fourteen
# theorem are unnecessary. Keep the support-poset theorem for arbitrary cuts.
f='support_families/elementary-support-family-proofs.md';s=read(f)
a=s.index('## 1.');b=s.index('## 2.',a)
s=s[:a]+'''## 1. The common-corner support

For colours $a,b,i,j,k$, the six cuts containing $a\\to b$ are
$C(ai),C(aj),C(ak),C(aij),C(aik),C(ajk)$.
Only this support description is needed from the common-corner alternative
here; its numerical assembly lemmas are proved separately.

'''+s[b:]
s=s.replace('This note concerns fourteen adjacent-repeat cubes.',
 'The support-poset statement concerns arbitrary adjacent cuts. The butterfly\nprofile statement concerns fourteen adjacent cubes with class cap three.')
s=s.replace('The six cuts are\n', 'Assume every class has at most three copies. The six cuts are\n')
a=s.index('We use the established six-class lemma:');b=s.index('## 0.',a)
s=s[:a]+'''A robust triple in a failure must use each of its three allowed repeats
once. If another source has pole pair Q meeting its pole pair P in one
colour, that source must repeat the colour in $P\\setminus Q$. Otherwise
it shares an allowed repeat with a member of the triple, and the two
sources fill the robust target's bicoloured positions.

'''+s[b:]
a=s.index('The shared-four pair bounds include');b=s.index('### The low cuts are robust',a)
s=s[:a]+'''Each block contains three classes of capacity three. Thus $L,R\\ge5$.

### Two completion criteria

**Low cuts are robust.** For U, the arcs $10,20$ have the common
source pool $C_3\\cup C_4\\cup U$, of size $R\\ge5$. Each other arc's
pool omits at most two high classes and therefore has at least eight
sources. After any two reservations, a set confined to $10,20$ has
at least three neighbours, while a set meeting any other arc has at
least six. Hall proves robustness of U; the argument for V is symmetric.

**High cuts have a completion when their block weight is at least six.**
For C_1, after the two bicoloured reservations suppose at least two
C_1 copies remain. Use two for its private arcs $02,12$. The four
remaining arcs have pools

    03,04: C_1,C_2,V;
    13:    C_1,C_3,U,V;
    14:    C_1,C_4,U,V.

The first pool has size L; each singleton pool has at least
$14-3-3=8$ sources. Removing the four reserved copies leaves at
least two neighbours for a subset of $03,04$ when $L\\ge6$,
and at least four for any subset meeting $13$ or $14$. Hall
completes the four positions. The other high cuts are symmetric.

'''+s[b:]
s=s.replace('Because all high counts are at most three,\nthe remaining conditions in (4) are automatic. Every high target',
 'Every high target')
a=s.index('### The low cuts are robust');b=s.index('### Both block weights',a)
s=s[:a]+'''### The low cuts are robust

Each block contains three classes of capacity three. Since $L+R=14$,
both block weights are at least five. The low-cut completion criterion
therefore makes both low cuts robust. In a failure, each uses every
repeated colour at most once.

'''+s[b:]
s=s.replace('Now all six counts are at most three, so `L,R>=5`. Suppose `L=5`.\nThen (5) again holds, with `x_1,x_2<=3`. As before `C_1` repeats only\n`2`, `C_2` only `1`, and the high cuts `C_3,C_4` have safe completion.',
 '''Suppose $L=5$. Then $R=9$, so $x_3=x_4=u=3$.
The robust low class U uses repeats $0,3,4$. Its repeat-restoration
constraint forces every C_1 source to repeat 2 and every C_2 source to
repeat 1. The high cuts C_3,C_4 have safe completion by their block
weight nine and the displayed high-cut criterion.''')
a=s.index('**Theorem 2.**');s=s[:a]+'''**Butterfly profile lemma.** A failing fourteen-pool in this family,
with every class of multiplicity at most three, has profile
$3,3,3,3,1,1$. No repeated-colour enumeration is needed for this statement.
'''
save(f,s)

# Make the use of the weakened butterfly theorem explicit. The pure
# concentration proofs have no dependency on this six-repeated-class result.
f='root/six-doubled-classes-hand.md';s=read(f)
s=replace(s,'Select two copies from six such classes.',
 '''In a hypothetical failure, pure concentration first bounds every class
by three: use `six-adjacent-elementary.md`, `pure-five-class-hand.md`,
and the four-copy proofs `../pure_supported/g4-row-hand.md`,
`../pure_supported/g4-hook-disjoint-hand.md`,
`../pure_supported/g4-exception-hand.md`. None uses this corollary.
Select two copies from six such classes.''')
s=s.replace('Otherwise the elementary\nsupport-family classification places',
 'Otherwise the support-poset theorem in\n`../support_families/elementary-support-family-proofs.md` places')
s=s.replace('its previously proved\nclassification says that a failure has class counts 3,3,3,3,1,1.',
 'the cap-three butterfly profile lemma in the same reference says that\na failure has class counts 3,3,3,3,1,1.')
save(f,s)

# The consequences here repeat the main article and create a reference cycle
# back from a prerequisite to the final synthesis. Keep only theorem + proof.
f='root/three-opposites-eleven-adjacent.md';s=read(f)
s=s[:s.index('## Consequences')]
save(f,s)

# The repeated-colour and compression notes are handled by MAIN in the
# assembler. Their used statements are already proved in the main article;
# their unused four-class table and applications do not enter the appendix.
unused=BASE/'overrides/three_opposite_root/repeated-colour-closures.md'
if unused.exists():unused.unlink()
f='elementary_alternative_next/private-column-row-opposite.md';s=read(f)
s=s[:s.index('Consequently, in the one-opposite fifteen-cube problem,')]
save(f,s)
print('Wrote eleven dependency-focused editorial overrides.')
