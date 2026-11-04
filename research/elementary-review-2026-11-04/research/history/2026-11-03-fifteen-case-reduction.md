# What remains for a direct elementary proof with fifteen cubes

The pure-fifteen theorem permits a direct attack on N5=15 without
first proving W=36 for every fourteen-failure. This note records the
exact remaining cases for that route. It assumes only the completed
elementary lemmas listed below, not the exhaustive failure catalogue.

## 1. Concentrated opposite varieties are already excluded

The earlier hand classifications say that a fourteen-failure containing
an opposite variety of multiplicity at least three has one of these
forms:

* Four copies of one opposite variety, no other opposite sources,
  and adjacent class sizes5,5.
* Three copies of one opposite variety, no other opposite sources,
  and adjacent class sizes5,3,3.

No opposite variety can occur five times in a fourteen-failure.
See `o4-elementary.md` and `o3-covers-guide.md` for the proof chain.

Suppose a fifteen-failure contained at least three copies of an opposite
variety. Five copies could be retained in a fourteen-subpool, impossible.
Thus its maximum opposite multiplicity is three or four. There is no
second opposite variety, since a fourteen-subpool retaining both types
would contradict either classification above.

If there are four opposite copies, delete each of the eleven adjacent
cubes in turn. Every deletion has adjacent profile5,5, so its statistic

    A = Σ_j binom(g_j,2)

equals20. Every pair of adjacent physical cubes survives nine of the
eleven deletions. Hence9A_15=11·20=220, impossible for an integer A_15.

If there are three opposite copies, delete each of the twelve adjacent
cubes. Every deletion has profile5,3,3, hence A=16. Each adjacent pair
survives ten deletions, giving10A_15=12·16=192, again impossible.

Consequently every opposite variety in a hypothetical fifteen-failure
occurs at most twice.

## 2. The all-adjacent and large-opposite cases are solved

If no opposite source occurs, `pure-fifteen-elementary.md` proves an
assembly.

If at least eight opposite sources occur, select eight and use
`eight-opposite-elementary.md`.

If exactly seven occur, use those seven and any adjacent source,
by the corollary in the same note.

If exactly six occur, an adjacent class of size at least three gives
the nine-source construction in
`../opposite_small_lemma/six-opposites-three-adjacent.md`.
Otherwise all adjacent class counts are at most two. Select eight of
the nine adjacent cubes and use
`../opposite_small_lemma/six-opposites-eight-adjacent.md`.

If exactly five opposite sources occur, an adjacent class of size at
least three is covered by the earlier five-opposite/triple-class
arguments: retain the five opposite sources, the triple, and six
other adjacent sources. Otherwise select nine of the ten adjacent
sources and use `five-opposites-nine-adjacent.md`.

If exactly four opposite sources occur, every adjacent class has
size at most three by the mixed concentration result explained in
Section 3. Select ten of the eleven adjacent sources and apply
`four-opposites-ten-adjacent.md`. The opposite variety cap two was
already proved in Section 1. This gives an assembly.

Thus a hypothetical fifteen-failure has between one and three
opposite sources.

## 3. Adjacent multiplicity bounds in those cases

Every adjacent class has size at most three. Four cubes of one class
and at least one opposite source can be retained in a fourteen-subpool;
the completed mixed concentration results exclude that subpool.

The exact direct-fifteen residual is therefore:

| Opposite total | Opposite-variety multiplicity | Adjacent-class multiplicity |
| ---: | ---: | ---: |
| 1,2,3 | at most2 | at most3 |

The bounds are necessary conditions for a hypothetical failure, not
asserted examples. No elementary exhaustion of these rows is claimed.

## 4. The alternative fourteen-failure identity route

For the original W=36 strategy, one additional pure branch remains:
fourteen adjacent cubes with a unique own-orientation looped triple.
The direct-fifteen deletion proof bypasses that classification problem.

The mixed fourteen-failure residual has the same opposite totals1–3
and the same class bounds as the table, but one fewer adjacent source.
The opposite-total-five branch is now closed by the replacement lemma
and the old grid constructions; see `five-opposites-nine-adjacent.md`.
The opposite-total-four capped branch is closed by
`four-opposites-ten-adjacent.md`. Combining it with the old
concentrated-opposite classification shows that every fourteen-failure
with four opposite cubes has four copies of one variety and adjacent
profile 5,5. Its invariant is W=3·20−4·6=36.

Finishing the direct-fifteen table would prove N5=15 without needing
the global W identity. Finishing the fourteen table and its unique-loop
pure branch would additionally give the desired failure classification
and identity.
