# Five opposite sources with two neighbouring pairs

**Status: elementary proof.** This is an eight-source construction.

**Lemma.** Let \(P,Q\) be opposite varieties sharing four directed
corners, and let \(R\) be any other opposite variety. The sources

\[
2P+2Q+R+2A+B
\]

assemble an opposite target whenever \(A,B\) are different adjacent
tricolour classes.

Write

\[
I=P\cap Q,\qquad J=P\setminus Q,\qquad K=Q\setminus P,
\qquad T=P\mathbin\triangle Q.
\]

Here \(I,J,K\) are two-edge sets, with each edge denoting both of its
directed corners. The line targets are \(P=I\cup J\),
\(Q=I\cup K\), and \(T=J\cup K\). Their union is a bidirected
\(K_4\) or \(K_{2,3}\).

## 1. Adjacent restrictions to a line

An adjacent cut uses at most one direction of an undirected edge.
It therefore meets each of \(I,J,K\) in at most two positions.
Its intersection with any opposite target has size two or four.
Consequently its three block counts are precisely one of

\[
(1,1,1),\qquad (2,2,0)\text{ and its permutations},\qquad (2,2,2).
\]

Moreover a restriction with counts \((1,1,1)\) determines the
adjacent class uniquely. On a \(K_4\) line union its three cut edges
form a directed star; their orientation fixes the cut on the four
vertices, and the fifth colour must join the singleton side to make
the side sizes two and three. On a \(K_{2,3}\) line union a three-edge
cut meets all five vertices, so its directions determine both sides
of the cut.

For \(R\) outside the line, exactly one of \(P,Q,T\) is its high
target: its intersections with the line targets have two, one and
one undirected edges respectively. We consider its high target first.

## 2. R has high target P or Q, or R=T

Interchange \(P,Q\) if necessary to make the high target \(P\).
The five opposite sources can fill the five unreserved target corners
whenever the three holes reserved for the adjacent sources satisfy
one of these conditions:

| Target | Sufficient distribution of the three holes |
|---|---|
| \(P=I\cup J\) | At least one hole in \(J\) |
| \(Q=I\cup K\) | At least two holes in \(K\) |
| \(T=J\cup K\) | One hole in \(J\), two in \(K\) |

These rules follow directly by allocating the two copies confined to
one block first. On \(P\), the two \(Q\) copies require two \(I\)
positions; \(R\) sees an edge in each of \(I,J\), and the two \(P\)
copies are universal. If exactly one hole lies in \(J\), then
\(R\) and the two \(P\) copies fill its three remaining positions.
If two or three holes lie in \(J\), its remaining positions use
\(P\) copies, while \(R\) fills an available \(I\) corner.
On \(Q\), \(R\) sees one \(I\) edge, and the two or three holes
in \(K\) leave that edge available. On \(T\), the two \(P\)
copies and \(R\) fill the three remaining \(J\) positions, and the
two \(Q\) copies fill \(K\). The same three sufficient rules hold
when \(R=T\): on \(P\), assign \(R\) an available \(J\)
position, the two \(Q\) copies to \(I\), and the two universal
\(P\) copies to the remainder. The inequality on the holes leaves
at least one \(J\) and two \(I\) positions. The argument on
\(Q\) is symmetric, and on \(T\) the source \(R\) is universal.

If \(A\) has block counts \((1,1,1)\), write its corners as
\(a_I,a_J,a_K\). If \(B\) has a \(P\)-corner outside
\(\{a_I,a_J\}\), reserve those two corners for the \(A\) copies
and the new corner for \(B\); the first rule applies. Otherwise
\(B\)'s \(P\)-intersection is exactly \(\{a_I,a_J\}\), and
its block counts must also be \((1,1,1)\). If its \(K\) corner
differs from \(a_K\), reserve \(a_I,a_K\) and that new \(K\)
corner on \(Q\); the second rule applies. If it does not differ,
the two classes have the same three-corner restriction and hence are
equal, contrary to the hypothesis.

If \(A\) has two corners in both \(I,J\), use target \(P\).
The two \(A\) copies can choose distinct corners, including a
\(J\) corner, while avoiding any selected \(B\) corner.

If \(A\) has counts \((2,0,2)\), use \(P\) with the two
\(A\) holes in \(I\) when \(B\) has a \(J\) corner. Otherwise
\(B\) also has counts \((2,0,2)\); use \(Q\) with the two
\(A\) holes in \(K\) and a \(B\) hole in \(I\).

Finally suppose \(A\) has counts \((0,2,2)\). If \(B\) has
an \(I\) corner, use \(P\) with the two \(A\) holes in \(J\).
Otherwise \(B\) also has counts \((0,2,2)\); use \(T\) with
the two \(A\) holes in \(K\) and a \(B\) hole in \(J\).
This exhausts all adjacent block profiles.

## 3. R has high target T

Now \(R\) sees an edge in each of \(J,K\), and one edge in each
of the targets \(P,Q\). The following three completion rules suffice:

| Target | Sufficient distribution of the three holes |
|---|---|
| \(P\) | Two in \(I\), one in \(J\) |
| \(Q\) | Two in \(I\), one in \(K\) |
| \(T\) | At least one in each of \(J,K\) |

For the first rule, the two \(Q\) copies fill the two remaining
\(I\) positions; \(R\) and the two \(P\) copies fill the
three \(J\) positions. Only one \(J\) corner has been removed,
so \(R\)'s two-corner intersection there survives. The second
rule is symmetric. In the third rule the remaining block sizes are
three and two, and \(R\) joins the doubled variety on the larger
block. Again only one corner of that block was removed.

If \(A\) has counts \((1,1,1)\), first use \(T\). The two
\(A\) holes occupy its distinct \(J,K\) corners. Any new
\(B\) corner there gives the third hole and completes the assembly.
Otherwise \(B\) agrees on both corners and has profile
\((1,1,1)\). Since \(B\ne A\), uniqueness forces a different
\(I\) corner. On \(P\), use the two different \(I\) corners
and the \(A\) corner in \(J\).

If \(A\) has two corners in both \(J,K\), use \(T\), choosing
one \(A\) hole in each block while avoiding the chosen \(B\)
hole. If \(A\) has counts \((2,0,2)\), a \(B\) corner in
\(J\) permits two \(A\) holes in \(K\) on \(T\). If no
such corner exists, \(B\) also has profile \((2,0,2)\); use the
two \(A\) corners in \(I\) and one \(B\) corner in \(K\)
on \(Q\). The profile \((2,2,0)\) is symmetric. All cases
are now covered.

## Consequence

In a fourteen-pool with five diffuse opposite sources and an adjacent
class of size at least three, the opposite profile \(2,2,1\) is
settled whenever the doubled varieties share four directed corners.
There are other adjacent classes available, since the adjacent total
is nine and each class has multiplicity at most three after the
four-class case is removed. Select two copies of the triple class
and one source from another class, then apply the lemma.
