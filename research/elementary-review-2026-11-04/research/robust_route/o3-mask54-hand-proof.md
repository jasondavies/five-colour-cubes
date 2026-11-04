# The O3 Hall-cover case 54

This note gives a hand proof for one cover case. The eight tiny matching
constructions below were found by computation; the deductions from them are
ordinary integer inequalities and do not use enumeration of count vectors.
Each construction can be checked directly against the directed-corner model.

Use the root model's classes and opposite varieties. Let X=O60 have three
copies. Let A, B, C be adjacent classes 4, 10, 17, with counts a,b,c, and let
U=O64 and V=O73 have counts u,v. Thus

  a+b+c+u+v=11,

with a,b,c<=5, u,v<=3. The standard pair caps give

  a+c<=7, b+c<=7, c+u<=7, b+v<=7.

Specifically, a+c and b+c are bounded by the shared-four adjacent-class
lemma. The bounds c+u<=7 and b+v<=7 are the missing-colour-pair bounds for
the unordered colour pairs {2,4} and {1,3}, respectively, and follow
from the eight-plus-three lemma. These are independent inputs to the
argument.

Geometrically, A is the cut {0,3}->{1,2,4}, B the cut
{1,3}->{0,2,4}, and C the cut {0,1,3}->{2,4}.
The opposite sources X,U,V are the bidirected complete bipartite graphs
12|34, 03|24, and02|13, respectively. Here pq|rs means that every
directed edge between {p,q} and {r,s} is present, in both directions.

The following eight-cube pools have an opposite-repeat assembly regardless
of the repeated-colour labels of A,B,C:

| Core | Target |
| --- | --- |
| 3X+2A+2B+U | O71 |
| 3X+2C+U+2V | O61 |
| 2X+A+2B+C+2V | O73 |
| 3X+B+C+2U+V | O61 |
| 3X+A+B+3U | O74 |
| 3X+3A+U+V | O74 |
| X+A+B+2C+3V | O73 |
| X+2A+3B+2V | O73 |

The target names denote bidirected graphs O71=04|12, O61=13|24,
O73=02|13, O74=03|12. The following arc-to-source assignments verify
the cores in the same order as the table (each arrow consumes one cube):

1. 01:A,02:A,10:B,14:B,20:U,24:X,41:X,42:X.
2. 12:V,14:C,21:V,23:X,32:X,34:C,41:X,43:U.
3. 01:A,03:V,10:B,12:C,21:V,23:X,30:B,32:X.
4. 12:C,14:X,21:V,23:U,32:X,34:B,41:X,43:U.
5. 01:A,02:U,10:B,13:X,20:U,23:U,31:X,32:X.
6. 01:A,02:A,10:V,13:X,20:U,23:X,31:A,32:X.
7. 01:A,03:V,10:V,12:C,21:V,23:X,30:B,32:C.
8. 01:A,03:V,10:B,12:B,21:V,23:X,30:B,32:A.

## 1. A failure has u=0

Suppose u>=1. The first core implies a<=1 or b<=1.

If a<=1, then b+c<=7 and the total give u+v>=3.

* If v>=2, the second core forces c<=1. Since b+v<=7,
  a+c+u>=4, so u>=2. If c=1, then b>=3 and the fourth core
  applies. If c=0, then a+u>=4 forces a=1,u=3, and the fifth
  core applies (b>=4).
* If v=1, then u>=2. The total forces b,c>=1, so the fourth core
  applies.
* If v=0, then u=3 and b+c=8-a<=7, so a=1 and b+c=7.
  The fifth core applies.

It remains to consider b<=1 and a>=2. Again u+v>=3 follows from
a+c<=7.

* If v=0, then u=3, b=1 and a+c=7; the fifth core applies.
* If v>=1 and a>=3, the sixth core applies.
* Otherwise a=2 and v>=1. If v>=2 and c>=2, the second core
  applies. If v=1, the total and c+u<=7 force b=1,c+u=7;
  hence c>=4,u>=2 and the fourth core applies. The only other
  possibility c<=1 is impossible because
  c+u+v=9-b>=8 but c+u+v<=7.

Thus u=0.

## 2. A failure has v<=1

If v=2, the total and a+c,b+c<=7 imply a,b>=2. For c>=1
the third core applies; for c=0, a+b=9 implies a,b>=4 and the
eighth core applies.

If v=3, the same inequalities imply a,b>=1. For c>=2 the
seventh core applies. For c=1, a+b=7 and a,b<=5 give a,b>=2,
so the third core applies. For c=0, a+b=8 gives a,b>=3, so the
eighth core applies.

Consequently v<=1. Since a+c,b+c<=7,

  a>=4-v>=3, b>=4-v>=3.

## 3. A class of size at least four supplies an adjacent target

Now a+b+c=11-v>=10, so at least one class has size at least four.
Among its copies two have the same repeated colour; reserve them for the
two bichromatic corners of that class's target. The following six-corner
completions use only tricoloured corners and therefore ignore every
remaining repeated-colour label.

For A, the target corners are
01,02,04,31,32,34 (directed arcs). If a>=4 and c>=1, use A
for01,04; C for02; X for31,32; B for34. If a>=4 and v>=1,
instead use V for01 and A for02,04. If a=5, use three A for
01,02,04, two X for31,32, and B for34. When a=4, c+v>=1
follows from the total and b<=5, so these cases suffice.

For B, the corners are10,12,14,30,32,34. If b>=4 and c+v>=1,
use B for10,30; C or V for12; X for14,32; A for34. If b=5,
use three B for10,12,30; two X for14,32; A for34. Again the
total forces c+v>=1 when b=4.

For C, the corners are02,04,12,14,32,34. If c>=4, use two A
for02,04; two remaining C for12,14; X for32; B for34. Here
a>=3 and b>=3 ensure the required supplies.

Thus every pool in cover case54 is soluble. The earlier computation
enumerated13 opposite-failing count vectors in this case, but that number
is not used anywhere in this proof.
