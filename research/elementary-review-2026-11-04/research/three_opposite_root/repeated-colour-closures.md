# Small repeated-colour completions for the three-opposite problem

4 November 2026

These are elementary sufficient constructions, independent of any
inventory search. They do not assert that the families below exhaust
all opposite-target failures; that reduction is a separate task.

Use C(S)=S→Sᶜ for an adjacent tricoloured-corner class. Its pole pair
is the two-element side of the cut. A class is own-looped when the
remaining sources match its six tricoloured corners after two copies
have been reserved. All source copies in the matchings are distinct.

## 1. Two intersecting own-looped triples suffice

**Lemma.** Suppose two adjacent classes each occur at least three
times and are own-looped. If their pole pairs meet, the pool assembles
an adjacent target.

Choose three copies of each class. A repeated colour occurring twice
in either triple immediately solves its own target: the two equal-
repeat copies fill the bicoloured corners and the own-loop matching
fills the six tricoloured corners. Otherwise each triple uses all
three repeated colours allowed by its pole pair. The two three-element
sets share a colour r.

Call the classes U,V. Since their pole pairs meet, the two poles of U
can be assigned to one U and one V source. Reserve one copy of each
repeating r. Start with the own-loop matching for U after two U
reservations. Restore one of those U copies and remove the reserved V.
If that V source was used in the matching, the restored universal U
copy replaces it. The six tricoloured positions remain matched, while
the two reserved sources provide the bicoloured corners of the U
target repeating r. This proves the lemma.

Consequently three own-looped triples always suffice: three disjoint
pole pairs would require six colours, whereas there are only five.

## 2. A nine-cube construction

**Theorem.** Let a,b,c,d,e be the five distinct colours. Let O be any
opposite-repeat source supplying the edge ab, in both directions.
Then the following nine-source pool always assembles:

    O + 3C(ac) + 3C(bc) + 2C(abc).

The same statement holds after reversing all directed cuts.

Write A=C(ac), B=C(bc), H=C(abc). Both triples are own-looped, by
the following assignments after reserving two copies of the target
class:

| Target class | Remaining target-class copy | Other triple | Two H sources | O |
| --- | --- | --- | --- | --- |
| A | cb | B:cd,ce | ad,ae | ab |
| B | ca | A:cd,ce | bd,be | ba |

Each row lists the target cut's six distinct corners. No source class
is used beyond its available multiplicity. The pole pairs ac and bc
meet in c, so Section 1 completes the proof.

In the three-opposite normalization

    P={01,02,14,24}, Q={01,03,12,23},

this gives in particular

    P + 3C(03) + 3C(13) + 2C(013).

Neither the second opposite variety nor any additional adjacent
helper is needed for this construction.

## 3. Four explicit four-class families

Continue with the displayed P,Q. Take one source of each opposite
variety; additional copies are harmless. Consider any one of the
following four adjacent-class families, or its global reverse:

| Family | Four classes |
| --- | --- |
| I | C(02), C(12), C(024), C(012) |
| II | C(03), C(123), C(13), C(013) |
| III | C(03), C(123), C(023), C(23) |
| IV | C(03), C(034), C(13), C(013) |

**Lemma.** If each of the four classes occurs at least twice and
three of them occur at least three times, these sources assemble.

For each family, every class occurring three times is own-looped.
The table below gives a six-corner matching after two of its copies
are reserved. Each assignment uses at most one remaining copy of
the target class, at most two of every other class, and at most one
P and one Q. A source name followed by two corners denotes two
distinct copies of that source class.

| Family | Target class | Six-corner matching |
| --- | --- | --- |
| I | C(02) | C(02):24; C(12):23; C(024):21,03; C(012):04; P:01 |
| I | C(12) | C(02):24,23; C(12):20; C(012):14,13; P:10 |
| I | C(024) | C(02):01,03; C(12):23; C(024):43; P:41; Q:21 |
| I | C(012) | C(02):24,23; C(12):14,13; C(024):03; C(012):04 |
| II | C(03) | C(03):31; C(123):34; C(13):32; C(013):04,02; P:01 |
| II | C(123) | C(03):34; C(123):24; C(13):30,14; P:20; Q:10 |
| II | C(13) | C(03):34,32; C(123):30,14; C(13):10; C(013):12 |
| II | C(013) | C(03):34,32; C(123):14; C(13):12; C(013):04; P:02 |
| III | C(03) | C(03):34; C(023):01,04; C(23):31; P:02; Q:32 |
| III | C(123) | C(03):34; C(123):30; C(023):24; C(23):20; P:14; Q:10 |
| III | C(023) | C(03):34,31; C(123):24; C(023):04; C(23):21; P:01 |
| III | C(23) | C(03):34,31; C(123):30,24; C(023):21; C(23):20 |
| IV | C(03) | C(03):34; C(034):32,31; C(013):02,04; P:01 |
| IV | C(034) | C(03):01,31; C(034):42; C(13):32; C(013):02; P:41 |
| IV | C(13) | C(03):34,32; C(13):30; C(013):14,12; P:10 |
| IV | C(013) | C(03):34,32; C(034):02; C(13):14,12; C(013):04 |

Every incidence is read directly from its directed cut or from the
four edges of P,Q. Three classes are therefore own-looped triples,
and Section 1 gives an assembly. This proves the family lemma.

## 4. Application to the exploratory residuals

The exploratory three-opposite search leaves four-class profiles
3,3,3,2 in these families, up to reversal, together with a split
profile having

    3C(03)+3C(13)+3C(013)+C(123)+C(034)

or its reverse. The family lemma solves the former. The nine-cube
construction solves the latter without either singleton.

This paragraph describes how the lemmas will apply if the geometric
exhaustion is proved. It is not a proof of that exhaustion. The
constructions in Sections 1–3 are unconditional and have explicit
hand-verifiable assignments. The accompanying witness script checks
these assignments but is not needed as a premise.
