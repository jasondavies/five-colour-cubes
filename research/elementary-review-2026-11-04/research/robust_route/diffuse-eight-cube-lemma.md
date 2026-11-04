# A small finite lemma for diffuse opposite-repeat sources

**Status:** exhaustively checked by a short standalone integer program.
An elementary proof has not been obtained, and this is not a Lean
kernel replay. It does not by itself complete the fourteen-cube
classification or the invariant proof.

## Lemma

Take eight cubes, at least five of them opposite-repeat cubes. Suppose
no opposite variety occurs more than twice. Then an opposite-repeat
target can be assembled, with the following possible exception:

* there are exactly five opposite-repeat sources; and
* all three adjacent-repeat sources have the same tricolour class.

The statement does not say that every pool of the exceptional form
fails. It says that failure implies this form.

## Exact check

`diffuse_eight_cube_check.cpp` constructs all twenty directed cut source
classes and fifteen bidirected K2,2 source/target types directly on five
colours. It has no data-file or external-library dependency.

Every pool in the lemma contains a five-opposite subpool with each
multiplicity at most two. There are9,828 such labelled subpools, forming
106 colour-permutation orbits. For each orbit representative the checker
adds every unordered triple of the35 coarse source types. It discards
triples violating the global opposite multiplicity bound and tests all
fifteen opposite targets by exact augmenting-path bipartite matching.

Output:

    Five-opposite colour orbits:106
    Eight-cube checks with global opposite cap2:757076
    Exceptions (all three adjacent sources share a class):222
    Verified the stated finite lemma.

Colour permutations can reverse the orientation convention for cyclic
corners. This causes no omission: opposite source sets are symmetric
under arc reversal, and the complete set of twenty directed cut classes
is closed under both colour permutations and global reversal.

The counts are representative checks, not numbers of labelled physical
failures. The repeated colours within adjacent classes play no role
because only opposite targets are tested.

## Consequence for a fourteen-cube failure

Assume the already established class bound g_j<=5 and suppose every
opposite variety occurs at most twice.

If at least six opposite cubes are present, select six of them and any
two other cubes. Their eight-cube subpool is not of the exceptional
form and therefore has an opposite-target assembly.

If exactly five opposite cubes are present, the other nine cubes are
adjacent-repeat. Since no one tricolour class contains all nine (indeed
each contains at most five), select three adjacent cubes that are not
all in the same class. Together with the five opposite cubes they form
a nonexceptional eight-cube pool, again yielding a solution.

Thus the finite lemma reduces the diffuse branch to at most four
opposite-repeat cubes in total.

## Why the class condition matters

Without a concentration bound on adjacent classes, five opposite
sources alone do not force an opposite-target assembly, even in a much
larger pool. For example, take9copies of root class6 (poles{0,4},
outward orientation), one O72 and two each of O73,O74. No opposite
target can be assembled. The complete14-pool does have an adjacent
target, as it must once one class contains at least six copies.
