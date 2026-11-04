# Three opposite copies and the butterfly support

This is a hand classification of the first four-corner Hall-cover orbit
for a fourteen-failure containing three identical opposite copies.
It uses the established adjacent-class bound five. Other Hall-cover
orbits are treated separately; this note does not assert completeness
of the full fourteen-failure classification.

Use O=±{13,14,23,24} and adjacent cuts

    H1=C(01), H2=C(02), H3=C(124), H4=C(123),
    U=C(12), V=C(012).

Let their counts be x1,x2,x3,x4,u,v, totaling eleven. The three copies
of O are additional. Put L=x1+x2+v, R=x3+x4+u, so L+R=11.

## Elementary assembly rules

1. If u≥4 or v≥4, two copies in that low class have the same repeated
   colour. Reserve them for the two bicoloured corners. Two further
   copies fill the two corners involving colour0. Three O and any
   remaining adjacent copy fill the other four corners. Thus u,v≤3.

2. If xi≥4 and its side total is at least six (L for i=1,2; R for
   i=3,4), reserve a same-repeat pair in Hi. Two remaining Hi copies
   fill its private pair of tricoloured corners. Two further copies
   from its side fill the other two corners outside O, and two O
   fill the last pair. For H1, these pairs are respectively
   {02,12}, {03,04}, and {13,14}.

3. If all four high classes are nonempty, form the opposite target
   ±{12,14,23,34}. One copy each of H1,H2,H3,H4 supplies
   12,21,43,34. Three O and one remaining adjacent copy fill
   14,41,23,32: every adjacent class in this family has 14 or23.

4. If exactly three high classes are nonempty, normalize x1=0.
   If x2+v≥2, build ±{03,04,23,24}: two copies from H2∪V supply
   03,04; H3,H4 supply40,30; three O and another adjacent copy
   supply23,32,24,42. Therefore failure forces x2=1,v=0.
   Then R=10 and u≤3, so one of x3,x4 is at least four;
   rule2 gives an assembly.

5. If exactly two high classes in the same block are nonempty,
   normalize these to H1,H2. If u≥2, build ±{01,02,14,24}:
   H2,H1 supply01,02, two U supply10,20, and three O plus one
   remaining adjacent copy supply14,41,24,42. Otherwise u≤1,
   L≥10 and v≤3, so one of x1,x2 is at least four; rule2 applies.

6. If at most one high class is nonempty, its bound five and u,v≤3
   force exactly the profile5,3,3; its side is at least eight,
   so rule2 again applies.

Consequently exactly two high classes, one from each block, are
nonempty. Normalize them to X=H1 and Y=H3, with counts x,y.

## Four numerical possibilities

We have x+y+u+v=11, x,y≤5 and u,v≤3. If x≥4, rule2 forces
x+v≤5, hence y+u≥6. If y≥4, rule2 would solve because its side
is at least six. Thus y≤3, and y=u=3, x+v=5. The symmetric
argument holds if y≥4. If both x,y≤3, the total forces three
counts3 and one count2.

Up to swapping the two sides, only the following possibilities remain:

| x | y | u | v |
|---|---|---|---|
| 2 | 3 | 3 | 3 |
| 3 | 3 | 2 | 3 |
| 3 | 4 | 1 | 3 |
| 3 | 5 | 0 | 3 |

## Repeated-colour pigeonhole

In all four rows, any two different nonempty classes among X,Y,U,V
must have disjoint sets of repeated colours. Otherwise their two
same-repeat cubes supply the bicoloured corners of an assemblable
target, as in this table:

| Reserved classes | Target cut |
|---|---|
| X,Y | Y in the first numerical row; X in the others |
| X,U | U |
| X,V | Y |
| Y,U | X |
| Y,V | Y |
| U,V | C(14) |

Here are explicit checks of the tricoloured completions. After the
reservations, X can be completed whenever at least two X copies and
at least four copies of X∪V remain: two X supply02,12; two further
X∪V supply03,04; and two O supply13,14. The corresponding rule for
Y requires two Y and four Y∪U, supplying40,43; 10,20; and13,23.
For target U, two Y∪U supply10,20, and three O plus any remaining
adjacent copy fill its four other corners. These numerical requirements
hold in every row where the indicated pair is present.

For the last pair U,V, their only possible common repeated colour is0.
Use their bicoloured corners with singleton1 and4. Three Y supply
10,40,43, one X supplies12, and two O supply13,42. This completes
the tricoloured cut C(14).

Moreover all copies within U have distinct repeated colours, and the
same holds within V. A same-repeat pair within U leaves at least two
Y∪U for its two corners involving0; three O and another adjacent
copy complete it. The analogous statement for V uses X∪V.

The number of distinct repeated colours required is therefore at
least 1+1+u+v. Only five colours exist. The first three rows require
8,7,6 respectively and are impossible. Only (x,y,u,v)=(3,5,0,3),
or its symmetric form (5,3,3,0), survives.

Hence every surviving coarse profile is three identical opposite
copies and adjacent-class sizes $5,3,3$. Only this necessary profile
is used in the threshold proof.
