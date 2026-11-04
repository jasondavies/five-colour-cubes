# Unfinished lead for the stronger eight-source lemma

**Status: discovery lead only.** This is not used in any completed
proof and has not received the independent audit given to the main
five-opposite/nine-adjacent theorem.

The stronger claim is that five opposite sources with variety cap two,
plus 2A+B with A and B distinct adjacent classes, always assemble.
It is now proved for opposite profile 2,2,1 in
`../five_opposite_profiles/two-pairs-two-adjacent-one.md`.

For the profiles 1,1,1,1,1 and 2,1,1,1, the virtual-triple reduction
and central-target construction leave only the case where B has the
same two-corner target intersection as A. If those two corners form
a directed star, the adjacent class is unique, so there is no such
distinct B. The possible exception consists of two opposite edges;
the fifth colour may join either side of the cut.

The holes agent supplied the following route just before the current
proof checkpoint was frozen. It still needs to be written carefully
and checked rather than cited as an established lemma.

Normalize A=C(01), B=C(014), and the central target to O73. For the
four-position grid cover, the opposite varieties are drawn from
{O61,O63,O68,O70,O73}.

- If an outer variety D other than O73 is doubled, try target D.
  Reserve its two A corners and B's additional corner. The two D
  copies are universal, and the other three opposite sources are
  distinct. The intended proof is a direct Hall completion.
- If O73 is doubled, among the three outer singles at least one
  of the pairs {O61,O68} or {O63,O70} is present. A target from that
  pair is proposed to solve the remaining corner conditions.
- If all five varieties are distinct, target O61 is proposed to
  have a uniform explicit assembly.

For the three-position grid cover, the line can be normalized to
{O63,O70,O73}, or its symmetric line {O61,O68,O73}, with one line
variety doubled and an outside S whose high line target is O73.
On target O63, reserve A at 03,04 and B at 42. The remaining positions
split into I={40,24} and J={30,23,32}. O70 is confined to I,
O73 and S meet J, and O63 is universal. The intended direct
allocation handles each choice of doubled line member.

These observations may give a compact completion, but the central
normalisation, Hall inequalities, and every allocation still need
an explicit audit. The current completed low-repetition theorem is
only O+2A+B+C for three distinct classes A,B,C.
