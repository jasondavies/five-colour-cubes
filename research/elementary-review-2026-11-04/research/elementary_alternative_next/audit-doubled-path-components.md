# Independent audit of the doubled-opposite path components

4 November 2026

**Outcome: PASS.** This audit covers

- `../three_opposite_double/one-change-path-hand.md`;
- `../three_opposite_double/alternating-path-hand.md`;
- `../three_opposite_double/three-opposites-one-double-hand.md`.

The first two notes were checked as mathematical arguments, including
all Hall inequalities, source reservations, count reductions and
repeated-colour dependencies. The joining note was checked against
the hypotheses and conclusions of its previously root-audited
four-cover and missing-bidirected-edge components. No unproved
inventory classification is used in these three notes.

## 1. The marked-single normalization

The doubled target is D=O60. A nonneighbouring single P shares
exactly one undirected D-edge, so a five-position containing set
has three missing directions on the other three edges. These
underlying edges form a path. Its direction words, up to reversing
the path and reversing every direction, have the three stated
forms: monotone, one change, alternating.

The normalizations retain both allowed P varieties. Directly closing
a four-cycle around the one shared edge gives O67/O72 for the
monotone and alternating representatives, and O64/O73 for the
one-change representative. The one-change proof handles its two
singles separately.

For the alternating representative, the permutation(1 3)(2 4)
followed by direction reversal sends

    32 ↦41, 41 ↦32, 42 ↦42.

It fixes D and exchanges O67 with O72. Thus this use of path reversal
preserves the fixed doubled variety and the forbidden pattern while
properly exchanging the marked single. No marked P choice is lost.

The three forbidden-cut lists are complete. In particular all four
monotone classes contain13, exactly as needed for the common-corner
eleven-source lemma.

## 2. One-change proof

For P=O64, the seven intersections with its six-position remainder
are correct. A set of k≤3 positions contains at most k entire
class patterns. Hence a König cover of size four using k≤3
position vertices covers at most3k+(4−k)≤10 of the eleven
adjacent copies. The resulting four-position containment is forced.
The six missing-pair rows are exactly those with capacity at least
eleven. Their four counts are3,3,3,2, so the displayed constructions
use only guaranteed copies. The fifth row has common corner10.
All five explicit opposite assemblies are valid.

For P=O73, after its21 and one D's41 are reserved, the table on
the remaining six positions is correct. The proposed criterion
x=e+h>0 and c+y=c+f+g>0 is sufficient. Sets containing12 see
at least11−c≥8 adjacent sources. Among the other five positions,
34 and43 give the two stated singleton conditions. The only
additional triple inequalities are

    a+b+x≥2, a+c+x≥2, b+c+x≥2.

Their complementary groups have capacity at most nine. The worst
four-position neighbourhood is12−y≥6; all others have at least
12 minus one capped class. This checks every remaining Hall subset.

The zero cases c+y=0, b=0 and c=0 really have the asserted common
corners. In the final b,c>0 branch, a+g≥2 follows from the cap
on b,c,f. The two selected A/G sources supply02,03, and the last
12 source exists among at least eight A/B/F/G copies after at most
three of those copies have been used. Source distinctness is valid.

## 3. Alternating proof

### The c=0 branch

After choosing an E/H source at30, ten adjacent sources remain on
03,04,23,24. The only singleton conditions are the stated support
of03 and23. The possibly small pair neighbourhoods are bounded
by a+X+f≥2 and a+X+e≥2; all others contain one of these
neighbourhoods or at least ten minus a single class. The sole triple
not meeting all remaining sources is03,04,23, whose neighbourhood
is11−Y≥5. The Hall argument is therefore sound.

Each zero case is valid: the first has common corner24, the second
has four counts3,3,3,2 and the stated O71 assignment, and the third
has b+f≥2 and a+e+h≥5. The last source at14 remains available
after the A,F reservations.

### The c=1 branch

The virtual source on{04,23} is legitimate. Assigning it04 uses
P there and C at40; assigning it23 uses C there and P at40.
If it is unused, one of C,P is put at40 and the other discarded.
Neither of these two physical sources appears elsewhere.

After the source at30 is selected,03 has positive support and24
has at least six adjacent neighbours. The virtual source gives the
two possibly small pairs their second neighbour. The triple
03,04,23 has at least the stated10−Y≥4 neighbours (in fact
one more if the virtual source is counted). All remaining Hall
inequalities hold.

In the d=g=0 subcase with a>0, the final14 and24 neighbourhoods
are at least three and six after all previous reservations. The
two distinct helpers therefore exist. If a=0, all four remaining
classes are positive and the displayed P-target assignment works.

In the a=b=h=0 subcase, f≥2 gives the stated assembly. If f=1,
the other three counts equal three. The cited nine-source lemma
applies with the two pole pairs12 and23, union class123, and D's
edge13. The other singleton classes are unnecessary. This invokes
an independent sufficient construction, so there is no circular
use of the theorem being proved.

### The c≥2 branch

The K-patterns are correct. Eight or nine sources cannot have rank
at most two with a König cover using one corner and one source:
the largest singleton containment is six copies at04. Thus all
patterns lie in a two-position set. The four table rows are exactly
the two-position sets accommodating at least eight sources.

Each row has three classes with counts at least two; with C the
full profile is3,3,3,2. The second and fourth rows have the stated
common corners13 and20. The third has disjoint classes A,H, each
occurring twice and at least one occurring three times, contradicting
the previously established disjoint-source bound. The first row's
explicit O61 assignment is valid.

## 4. Joining argument and machine check

The two universal D sources reduce failure to matching rank at
most five for the other twelve sources. The prior four-cover theorem
then supplies a five-position containing set. The prior bidirected
theorem handles every missing complete edge, including all neighbouring
D,P cases. The remaining three path forms are precisely the cases
audited above. The proof therefore establishes the stated theorem
for two copies of D, one distinct P, and eleven capped adjacent cubes.

`audit_doubled_path_geometry.py` independently checks the exact cut
and marked-single lists, the three path-form coverage of the32
oriented three-edge subsets of D, the alternating symmetry, the
König containment tables, and nine fixed eight-source assignments.
Its result is in `doubled-path-geometric-audit.json`: all checks pass.
This checks fixed geometry, not source inventories. The Hall and
count arguments above were audited directly as proofs.
