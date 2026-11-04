# Independent audit of the five-opposite target

## Verdict

The argument in `../root/five-opposites-nine-adjacent.md` is valid as
an elementary proof, with the previously written geometric lemmas as
explicit inputs. Its stronger nine-source helper lemma is valid too:

> Five opposite sources with variety cap two, together with 2A+B+C
> for three pairwise different adjacent tricoloured-corner classes
> A,B,C, contain an opposite assembly. One of O+2A+B and O+2A+C
> already assembles.

The universal eight-source statement O+2A+B for every B≠A is not an
input to this audit. Nor is the old exhaustive eight-source check.

## 1. The replacement lemma

An opposite target has four undirected edges, each supplying its two
directions. Three cubes in one adjacent class occupy three different
edges, since the class has at most one direction of any edge. Every
adjacent cut meets a target cycle in at least two edges: a cut of a
cycle has even size, and all four cycle vertices cannot lie on the
same side of a partition of five vertices into parts of size two and
three. The three occupied edges and the helper's at least two edges
therefore overlap.

At an overlapping edge, the other direction is occupied by an opposite
source. Swapping the two assigned positions, if necessary, leaves that
source compatible and puts the helper at its available direction. The
other two adjacent sources are unaffected. Every cube still appears
once, and the assignment still uses eight distinct corner positions.

The three adjacent copies are interchangeable for this operation
because only their tricoloured corners are used; their individual
repeated colours are irrelevant. The operation does not require
reflecting a physical cube.

No multiplicity condition on the opposite sources is used in this
replacement lemma itself.

## 2. The low-repetition construction uses only two actual A copies

If a two-column rectangle has matching rank four among the five
opposite sources, four fill its reverse positions and the fifth fills
one forward position. Three hypothetical A copies fill the rest.
The replacement lemma then applies.

Otherwise the six-position grid has rank at most four. One can see
this directly without rank submodularity: any set of five grid
positions contains two complete columns. Matching all five would
match that four-position rectangle.

The Hall cover has three or four positions. With at most one doubled
opposite variety, a three-position cover containing four sources must
occupy all three columns and support a line 2P+Q+R. The fifth source
is outside it. A four-position cover cannot be a complete rectangle,
so its column counts are 2,1,1. These are exactly the two alternatives
in `../opposite_small_lemma/five-opposites-low-repetition.md`.

The central-target incidence claims hold in both alternatives. In
particular, its intersection with A is exactly two corners a,b; each
opposite source sees at least two target edges; every target edge
has at least two opposite copies; and, if the doubled variety D is
not the target, at least one of a,b is outside D's intersection.

For any five of the six positions left after reserving a,b, Hall
holds. A set using one edge sees at least two opposite copies. A set
using three edges sees all five. A set using two edges sees at least
four, except when the unique avoiding variety is doubled. In that
case a reserved corner is on those two edges, leaving at most three
available positions, which their three neighbours suffice to cover.

Thus the helper need only meet T\{a,b}. At most two adjacent classes
avoid that set: a two-corner star fixes a unique class, while two
opposite edges allow only the two choices for the fifth colour.
One avoiding class is A itself. This last inclusion is essential to
the nine-source helper lemma and has been checked explicitly.

## 3. Two doubled opposite varieties

For neighbouring doubled varieties, the existing construction accepts
2A+B whenever B≠A, so either of the two different helpers works.

For nonneighbouring doubled varieties, the full grid classification
in the earlier note has one overlapping normal form and three
disjoint normal forms. The third hypothetical A copy occurs only
when a rectangle is immediately matched, which is handled by the
replacement lemma. Every other final construction uses exactly two
A copies, all five actual opposite sources, and a single helper.

In the overlapping normal form, the two A copies and the singleton
opposite source occupy three fixed corners. The two doubled varieties
can fill any four of the five remaining corners. The helper rescue
set is those five remaining corners; at most two adjacent classes
avoid it, including A.

In a disjoint normal form, one completion works when the helper meets
an edge e absent from the two doubled varieties. A second completion
works when it meets one of three other specified corners. Their
union E consists of two bidirected edges and a directed edge joining
their components. Every adjacent cut avoiding the bidirected edges
must keep their endpoints together. The further direction fixes the
orientation, leaving at most two cuts. Again A is an avoiding class.

There is no source reuse in either completion. The first assigns the
singleton opposite source to one direction of e, the helper to the
other, the two A copies to their two distinct target corners, and
the four doubled opposite copies to the remaining four corners. The
second assigns the other doubled variety to the common bidirected
edge, the singleton opposite source to a reverse A corner, both A
copies to their target corners, the helper to a remaining corner,
and the target's doubled variety to the final two positions.

## 4. The helper and fourteen-source deductions

In every hard case, at most two classes avoid the rescue set, one
being A. Two helpers in distinct classes B,C, neither equal to A,
cannot both avoid it. Therefore O+2A+B or O+2A+C assembles.

For nine adjacent sources with class cap two, either all nine classes
are different, and the existing nine-distinct-class theorem applies,
or some class is doubled. There are at least five occupied classes,
so two distinct helper classes can be selected. This proves the
requested five-opposite, nine-adjacent theorem.

## 5. Separate geometric checks

`audit_five_target.py` independently checks the small geometric inputs
and displayed assignments. It does not enumerate fourteen-source
inventories. The successful checks include:

- all fifteen opposite patterns on the fixed adjacent grid;
- the two four-position and two three-position grid normal forms;
- 72 line/central-target completion checks;
- 180 two-corner avoider checks;
- the one overlapping and three disjoint nonneighbouring normal forms;
- 46 rescue sets, each avoided by at most two classes including A;
- 148 overlapping and 222 disjoint helper assignments.

Results are recorded in `five-target-audit.json`.

The earlier `rescue_patterns.cpp` computation in this directory was
used only to discover the extent of the stronger eight-source claim.
Its inventory output is not used as a premise of this proof.

## Expositional suggestion

Replace the sentence invoking matching-rank submodularity by the
five-position observation in Section 2 above. It gives the required
rank bound immediately and reduces the formal prerequisites.
