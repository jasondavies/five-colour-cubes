# No triple in a failing pure fourteen-pool has a private row pair

**Lemma.** Consider a failing pool of fourteen adjacent-repeat cubes,
with every tricoloured class of multiplicity at most three. No triple
class has two private corners in one row of its two-by-three cut array.
Consequently every triple without an own-orientation loop has exactly
two private corners.

This removes the all-private hypothesis from
`../root/g3-private-row-hand.md`. The dependencies are the already
proved nonprivate-triple lemma, the two-own-loop-triple exclusion,
the six-repeated-class bound, and the three common-corner lemmas.
None depends on the present extension.

## 1. The previous geometric reduction still applies

Normalize the triple to `A=C(01)` with private corners `02,03`, and
put `Q={2,3,4}`. The eleven possible outsider classes are

\[
P_i=C(1i),\qquad N_i=C(\{1\}\cup(Q\setminus\{i\})),
\qquad i\in Q,
\]

together with `H=C(023)`, `B=C(234)`, and
`Z_i=C(Q\setminus{i})`. Write `v` for the total P/N multiplicity,
`h` for the H multiplicity, and `z` for the total B/Z multiplicity.
Thus `v+h+z=11`.

Sections 1 and 2 of the previous row proof use no private-corner
hypothesis on the other triples. They establish `z<=3`.
Here are the key facts behind that step. Four zero-intersection
sources can match a two-row rectangle of the reverse-A array;
a nonzero outsider in the corresponding forward rectangle and
three A then finish an opposite target. At `z=4`, at most one
reverse row has degree below two; seven nonzero outsiders cannot
all be confined to the omitted forward column, whose singleton
classes have total capacity six. At `z>=5`, every reverse row has
degree at least two. If all eleven outsiders are zero, the three
Z classes have at least eight copies and match all six reverse-A
corners; repeated-colour pigeonhole using the A copies and a B
copy then solves an adjacent target.

Put `u=h+z`. The matching argument in Section 3 of the previous
proof, through its two final exceptional cases, also uses no
assumption about the private corners of other triples. It says
that `u>=2` gives an opposite assembly unless one of the following
occurs:

* `u=2`, `v=9`, with all common-corner sources in
  `P_i,P_j,N_k`, where `{i,j,k}=Q`. Each of those classes is a triple.
* `z=0`, `h>=2`, `j=4`, and all common-corner sources are
  `P_i,P_4,N_k`, where `{i,k}={2,3}`. Their total is `11-h>=8`.

For completeness, the matching reduction uses the reverse-A
0-column support `R` of the P/N sources. It has at least two rows.
Three P/N sources fill any two supported 0-column positions and
one forward corner on those rows: the last slot has degree at
least `v-3>=2`, and together with either 0-column slot sees every
P/N source. Two of the `u` sources fill the other reverse column
unless `R={i,j}` and all `u` sources miss row `j`. The latter
condition forces all zero sources to be `Z_j`, and permits H only
when `j=4`. If `z>0` and `u>=3`, retargeting the two rows `i,k`
completes the assembly. Exactly the two exceptions above remain.

## 2. The two exceptions need no all-private assumption

Whenever `A,P_i,P_j,N_k` are present, both `P_i` and `P_j` have
at most one private corner. For `P_i`, A covers its 1-row corners,
`P_j` covers `10`, and `N_k` covers `i0,ik`, leaving at most `ij`.
The statement for `P_j` is symmetric. The nonprivate-triple lemma
therefore makes either of these classes an own-loop class if its
count is three.

The first exception has two such triples. It contradicts the
two-own-loop-triple exclusion.

In the second exception, `h=2` likewise makes all three common
classes triples, giving the same contradiction. Thus `h=3` and
their counts sum to eight. If both `P_i,P_4` are triples, again
there are two own-loop triples. Otherwise `N_k` is a triple and
exactly one of `P_i,P_4` is a triple, with the other doubled.

If `P_4` is that triple, its own loop conflicts with the present
class `H=C(023)`, which has the same pole pair `14`. The looped
triple uses all three allowed repeated colours; H has no other
allowed repeated colour. This is impossible.

If `P_i` is the triple, its own loop uses all three repeated
colours outside its poles `1i`. Both A and H have pole pairs
meeting `1i`, so own-loop restoration makes them conflict with
`P_i`. Each A and each H must consequently repeat `i`.
Reserve one A and one H for an A target's bicoloured corners.
Its six tricoloured corners have the completion

\[
 A:02,03;\qquad H:04;\qquad P_4:1i;\qquad
 N_k:1k;\qquad P_i:14.
\]

All six sources remain available: A and H originally have three
copies each, and the other three classes are present. This is a
solution, another contradiction.

Thus `u<=1`, and hence `v>=10`.

## 3. Ten common-corner sources are now impossible

If all six P/N classes occur, the common-corner nine-cube theorem
applies. At most three present classes have capacity at most nine.
It remains to consider four or five present common-corner classes.

With five classes present, every one has at most one private
corner even within this family. Thus every triple among them has
an own loop, and at most one can be a triple. Their total is at
most eleven.

If the total is eleven, the counts are `3,2,2,2,2`; these five
repeated classes, together with A, violate the six-repeated-class
bound. If the total is ten and there is no triple, all five are
doubled, giving the same contradiction. The only remaining
profile is `3,2,2,2,1`, which always solves by
`common-corner-32221-hand.md`.

With exactly four common-corner classes present, at most one has
two private corners after A is included. This is the elementary
two-absence check at the end of the previous row proof: two
absent classes of the same kind can leave two private corners
only in the complementary class of the other kind; with one
absent P and one absent N, at most one N class keeps two, because
A covers every corner `1q`. Hence at most one triple can lack an
own loop. Since there is at most one own-loop triple as well,
the total is at most `3+3+2+2=10`.

Equality is required by `v>=10`. The profile is therefore
`3,3,2,2`, and at least one of its two triples has an own loop.
The lemma `../mixed_diffuse/common-corner-3322-own-loop-hand.md`
excludes exactly this case.

All possibilities have been excluded, proving the row-pair lemma.

## 4. Consequence for every non-own-loop triple

The nonprivate-triple lemma gives at least two private corners
to every triple without an own loop. Three private corners in
a two-row array would put two in one row, which has just been
excluded. Thus such a triple has exactly two private corners.

In particular `private-pair-promotion-hand.md` now applies to
every non-own-loop triple in a failing pure fourteen-pool: its
four nonprivate corners have an outsider matching, and adjoining
any source meeting a private corner creates an own loop.
