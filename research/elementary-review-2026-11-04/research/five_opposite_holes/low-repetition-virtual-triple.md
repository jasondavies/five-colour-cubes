# Five opposite sources of low repetition and a virtual adjacent triple

**Status: elementary proof.** Let O be five opposite source copies,
each variety occurring at most twice and with at most one doubled
variety. If A,B,C are three distinct adjacent tricoloured-corner
classes, then

    O + 2A + B + C

contains an opposite-target assembly. This is a nine-source lemma.
It proves the requested five-opposite, nine-adjacent statement for
opposite profiles 1,1,1,1,1 and 2,1,1,1.

The proof uses the existing grid geometry from
`../opposite_small_lemma/six-opposites-three-adjacent.md` and the
central-target completion argument from
`../opposite_small_lemma/five-opposites-low-repetition.md`.
No inventory enumeration is a premise.

## 1. Replacing one member of a hypothetical adjacent triple

**Replacement lemma.** Let O be five opposite source copies and let
A be an adjacent class. If O together with three A copies assembles
an opposite target, then O together with two A copies and any
adjacent source B assembles an opposite target.

Take an assembly using O and three A copies. Their eight cubes must
all be used. The three A corners lie on three distinct underlying
edges of its four-cycle target T: an adjacent cut has at most one
direction of each edge. Every adjacent source B meets an opposite
target on at least two underlying edges. Hence B has a compatible
corner on an edge e occupied by one of the three A copies.

If B has the same directed corner there, replace that A directly.
Otherwise the reverse corner on e is occupied by an opposite source:
no A copy can present the reverse direction. Move that opposite
source to the former A corner and put B at the reverse corner.
The move is legitimate because every opposite source is bidirected.
All other assignments remain in place. This gives the claimed
assembly using the five actual opposite cubes, two A copies, and B.

Thus failure of O+2A+B+C implies failure of the hypothetical
eight-source pool O+3A. Its third A need never be an actual cube.

## 2. The low-repetition grid alternatives

Assume O+2A+B+C fails, and normalize A's grid to

    02 03 04
    12 13 14.

The hypothetical pool O+3A also fails by Section 1. Therefore each
two-column rectangle in the grid has opposite-source matching rank
at most three. Otherwise four opposite sources fill its reverse
corners; the fifth opposite source and three A copies fill the
forward corners. Submodularity bounds the full grid rank by four.

Hall gives a grid subset H with

    |H| + #{opposite copies whose grid pattern is not contained in H} ≤ 4.

Each opposite grid pattern is either a two-position pair in distinct
columns or a complete two-column rectangle, and determines its variety
uniquely. Thus |H|≤2 is impossible under the opposite cap. If |H|=4
and H is a two-column rectangle, the five sources supported there
match all four positions, again impossible. The remaining alternatives
are exactly:

1. All five source patterns lie in four grid positions of column
   sizes 2,1,1.
2. Four source copies lie in three grid positions, and one source
   lies outside them. The three positions occupy distinct columns.

For (2), a three-position shape in only two columns supports only two
varieties, hence at most three sources when only one may be doubled.
The three-column shape therefore consists of 2P,Q,R on the three
two-position subsets, with a further variety S. The varieties P,Q,R
form a line, and S is outside that line: another copy of P exceeds
its cap and another Q or R introduces a second doubled variety.

## 3. Central target and five-source completion

The following central-target construction is proved explicitly in
the old low-repetition note, Sections 2–3. The geometric checks concern
just two four-position grid shapes and the two line types K4 and K2,3.

In alternative (1), take the target T determined by the two
singleton-column positions. In alternative (2), take the unique
line target T among P,Q,R in which S has a two-edge intersection.
In either case:

- every one of the five opposite copies meets at least two edges of T;
- every target edge is seen by at least two opposite copies;
- A meets T in exactly two corners, denoted a,b;
- if a variety D≠T is doubled, at least one of a,b lies outside D∩T.

After reserving a,b for the two actual A copies, the five opposite
sources fill any five of the remaining six positions. Here is the
Hall verification, included to make the exact needed consequence clear.

A position set supported on one target edge has at least two source
neighbours. A set using at least three target edges sees all five
sources. A set using two edges has at least four neighbours, except
possibly when the unique variety avoiding those edges is the doubled
variety D. In that event it has three neighbours, but the two edges
are T\D, and one of their four directed positions has already been
reserved as a or b. Thus only three of them remain. Every Hall
inequality for a set of at most five unreserved positions holds.

The case D=T creates no exception, because a universal target source
cannot avoid any nonempty set of positions.

## 4. One of B,C completes the target

An adjacent source whose T-intersection is contained in {a,b} must
have exactly that two-corner intersection, since every adjacent cut
meets an opposite target in at least two corners. At most two
adjacent classes have any specified two-corner T-intersection.

Indeed, if the two directed edges form a star, the three incident
vertices' cut membership is fixed and the fourth target vertex must
join the star's two leaves to avoid further crossing edges. The fifth
colour then joins the centre to give side sizes two and three. This
determines one class. If the two edges are opposite, the directions
fix a two-versus-two cut of the four target vertices, and the fifth
colour may join either side, giving two classes.

One of these at-most-two classes is A. Since A,B,C are pairwise
distinct, at least one of B,C has a target corner c outside {a,b}.
Use that source at c and the two actual A copies at a,b. The five
opposite sources fill the remaining five positions by Section 3.
All eight used sources are distinct physical cubes. This contradiction
proves the nine-source lemma.

## 5. Consequence for the requested fourteen-source pool

Take five opposite sources of either low-repetition profile and nine
adjacent sources with class multiplicities at most two.

If the nine adjacent classes are distinct, the established
nine-distinct-class theorem gives an opposite-target assembly. Otherwise
choose a doubled class A. At least five adjacent classes are occupied,
so choose two further distinct classes B,C. Select two actual A copies
and one actual source from each of B,C, and apply the nine-source lemma.

This closes both opposite profiles 1,1,1,1,1 and 2,1,1,1 in the
requested five-opposite, nine-adjacent theorem.

## Scope

The proof establishes O+2A+B+C when A,B,C are pairwise distinct.
It does not assert the stronger eight-cube statement O+2A+B for every
B≠A. In the central-target step, a distinct B could still have the
same two-corner target intersection as A. The additional distinct
class C removes that possibility. The nine adjacent sources in the
requested target provide more than enough class diversity.
