# The one-change missing path for 2D+P

4 November 2026

**Status: complete hand argument; independent root and alternative-agent
mathematical audits passed.**

Normalize D={13,14,23,24}. Suppose the eleven adjacent sources,
each class of multiplicity at most three, avoid24,31,41. These
directions have one change along the three-edge path2–4–1–3.

The eligible classes, with their counts, are

| Count | Class |
| --- | --- |
| a | A=C(01) |
| b | B=C(134) |
| c | C=C(124) |
| e | E=C(13) |
| f | F=C(14) |
| g | G=C(014) |
| h | H=C(013) |

The opposite sources are D,D,P. Containment in the corresponding
five-position D-cover forces P to be one of

    O64={02,04,23,34}, O73={01,03,12,23}.

Both choices are treated separately, so no symmetry of the marked
single variety is assumed. We use the common-corner eleven-source
theorem in `common-corner-eleven-hand.md`.

## 1. P=O64

In target P, the two D copies can fill23,32. Consider its other six
positions

    R={02,04,20,34,40,43}.

If the adjacent sources match any five of R, use P at the sixth and
the two D copies at23,32. Thus failure implies adjacent matching
rank at most four on R. The adjacent patterns on R are

| Class | R pattern |
| --- | --- |
| A | 02,04 |
| B | 40 |
| C | 20,40,43 |
| E | 34 |
| F | 40,43 |
| G | 02,43 |
| H | 02,04,34 |

Any one, two or three positions of R contain patterns from at most
one, two or three of these classes, respectively. For the only
nontrivial bound, a three-position set containing C's pattern admits
just B,C,F, while one containing H's admits just A,E,H. Otherwise
C,H are excluded. Among A,F,G, the pairs A,F have four positions
in union; A,G have three but contain neither singleton position;
F,G have three and contain only B's singleton position. Hence a
three-position set still admits at most three classes.

König's theorem now shows that all eleven patterns lie in a
four-position set. Indeed a cover with k≤3 corner vertices and
at most4−k source vertices covers at most3k+(4−k)≤10 copies.

Equivalently, two R positions are absent from the entire adjacent
pool. The only such absences leaving capacity at least eleven are
the six rows below. Every row has four eligible classes, necessarily
with profile3,3,3,2.

| Missing R positions | Eligible classes |
| --- | --- |
| 04,20 | B,E,F,G |
| 20,34 | A,B,F,G |
| 20,40 | A,E,G,H |
| 20,43 | A,B,E,H |
| 02,04 | B,C,E,F |
| 04,34 | B,C,F,G |

This table follows directly from the seven patterns above: every
other missing pair leaves at most three eligible classes.

The fifth row has all eleven sources through corner10, so the
common-corner theorem solves it. Each other row admits target
O63={03,04,23,24} with the explicit assignments below. Every
adjacent class is used at most twice, within its guaranteed count.

| Eligible classes | Eight-corner assignment |
| --- | --- |
| B,E,F,G | G:03; P:04; D:23,24; B:40,42; E:30,32 |
| A,B,F,G | A:03,04; P:23; D:24,42; B:30,32; F:40 |
| A,E,G,H | A:03,04; P:40; D:23,24; E:30,32; G:42 |
| A,B,E,H | A:03,04; P:23; D:24,42; B:32,40; E:30 |
| B,C,F,G | G:03; P:04; D:24,42; B:30,32; C:23,40 |

Thus P=O64 always assembles.

## 2. P=O73

Use target O61={12,14,23,34}. Put P at21 and one D at41. The
remaining D source sees14,23,32. The adjacent intersections on the
other six positions are

| Source group | Positions |
| --- | --- |
| A | 12,14 |
| B | 12,32 |
| C | 23,43 |
| E,H | 12,14,32,34 |
| F,G | 12,43 |

Put x=e+h and y=f+g. This target assembles whenever

    x>0 and c+y>0.                            (1)

For clarity, these are sufficient by the following full Hall
check. Any set containing12 has at least11−c≥8 adjacent neighbours.
For sets inside {14,23,32,34,43}, corner34 has x neighbours and
corner43 has c+y. The remaining D source meets14,23,32. The only
additional inequalities not immediate from (1) and the total count
are

    a+b+x≥2, a+c+x≥2, b+c+x≥2.

These hold because their respective complementary groups c+y,
b+y,a+y have capacity at most3+6=9, while the total is eleven.
All four-position sets have at least12−y≥6 neighbours or at
least12 minus one class; the five-position set meets all sources.
Thus every Hall inequality holds.

If c+y=0, only A,B,E,H occur, and all their sources contain12.
The common-corner theorem applies.

It remains x=0, so E,H are absent. The five possible classes are
A,B,C,F,G, with total eleven. If b=0, all present classes contain13.
If c=0, all contain12. Again the common-corner theorem applies.

Assume b,c>0. Since b+c+f≤9, there are at least two A/G sources.
Use target O72={02,03,12,13}, with

    D:13,31; P:21; C:20; B:30;
    two A/G sources:02,03;
    one further A/B/F/G source:12.

The last source exists: the four indicated classes have11−c≥8
copies, and only three have been used. Every such class contains12.
This completes the P=O73 case.

Both one-change configurations are therefore soluble, by explicit
geometric and count arguments rather than inventory enumeration.
