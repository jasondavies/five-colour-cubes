"""Small independent audits of the geometric proof, not inventory exhaustion.

Checks the two grid normal forms, the line incidence facts, and each
explicit rescue construction used by the five-opposite argument.
"""
from itertools import combinations, permutations
from collections import Counter
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'root'))
import cut_model as m

A = m.CUTS[0]
O = {i: m.CORNERS[i] for i in range(60, 75)}
stats = Counter()

def c(s):
    return ('t', int(s[0]), int(s[1]))

def rev(x):
    return (x[0], x[2], x[1])

def corners(*ss):
    return frozenset(c(s) for s in ss)

def bi(s):
    x = c(s)
    return frozenset((x, rev(x)))

def edge_count(xs):
    return len({frozenset((x[1], x[2])) for x in xs})

def matched(sources, positions):
    owner = [-1] * len(sources)
    pos = list(positions)
    def aug(k, seen):
        for i, source in enumerate(sources):
            if i not in seen and pos[k] in source:
                seen.add(i)
                if owner[i] < 0 or aug(owner[i], seen):
                    owner[i] = k
                    return True
        return False
    return all(aug(k, set()) for k in range(len(pos)))

def avoiders(E):
    return [j for j, cut in enumerate(m.CUTS) if not cut & E]

def check_rescue(E):
    av = avoiders(E)
    assert 0 in av and len(av) <= 2, (E, av)
    stats['rescue_sets_with_at_most_two_avoiders_including_A'] += 1

# Every source pattern is unique and is a two-position pair in different
# columns, or a complete rectangle.
patterns = {i: O[i] & A for i in O}
assert len(set(patterns.values())) == 15
for i, p in patterns.items():
    cols = Counter(x[2] for x in p)
    assert sorted(cols.values()) in ([1, 1], [2, 2]), (i, p)
stats['unique_grid_patterns'] = 15

# The two four-position shapes and their five-source central targets.
for H, T in [(corners('02', '12', '03', '04'), 63),
             (corners('02', '12', '03', '14'), 68)]:
    varieties = [i for i, p in patterns.items() if p <= H]
    assert len(varieties) == 5
    ab = A & O[T]
    assert len(ab) == 2
    for i in varieties:
        assert edge_count(O[i] & O[T]) >= 2
        if i != T:
            assert len(O[i] & ab) == 1
    for edge in {frozenset((x[1], x[2])) for x in O[T]}:
        assert sum(any(frozenset((x[1], x[2])) == edge for x in O[i])
                   for i in varieties) == 3
    check_rescue(O[T] - ab)
    stats['four_position_grid_shapes'] += 1

# The two three-position shapes, each giving one line of three cycles.
for H in [corners('02', '03', '04'), corners('02', '03', '14')]:
    line = [i for i, p in patterns.items() if p <= H]
    assert len(line) == 3
    assert all(edge_count(O[i] & O[j]) == 2 for i, j in combinations(line, 2))
    for S in O:
        if S in line:
            continue
        high = [i for i in line if edge_count(O[i] & O[S]) == 2]
        assert len(high) == 1
        T = high[0]
        assert sorted(edge_count(O[i] & O[S]) for i in line) == [1, 1, 2]
        ab = O[T] & A
        assert len(ab) == 2
        for P in line:
            src = [O[P]] + [O[i] for i in line] + [O[S]]
            assert len(src) == 5
            assert all(sum(x in s for s in src) >= 2 for x in O[T])
            assert all(edge_count(s & O[T]) >= 2 for s in src)
            if P != T:
                assert ab - O[P]
            rest = O[T] - ab
            assert all(matched(src, ps) for ps in combinations(rest, 5))
            stats['line_central_completion_checks'] += 1
        check_rescue(O[T] - ab)
    stats['three_position_grid_shapes'] += 1

# Adjacent classes confined to a two-position intersection: at most two.
for T in O:
    for ab in {cut & O[T] for cut in m.CUTS if len(cut & O[T]) == 2}:
        assert sum((cut & O[T]) <= ab for cut in m.CUTS) <= 2
        stats['two_corner_avoider_checks'] += 1

# Verify that the nonneighbouring doubled patterns have exactly the
# one-overlap and three-disjoint normal forms used in the written proof.
group = [p for p in permutations(range(5)) if set(p[:2]) == {0, 1}]
def transform(xs, p):
    return frozenset(('t', p[a], p[b]) for _, a, b in xs)
def canonical_pair(i, j):
    reps = []
    for p in group:
        a = tuple(sorted(transform(patterns[i], p)))
        b = tuple(sorted(transform(patterns[j], p)))
        reps.append(tuple(sorted((a, b))))
    return min(reps)
overlap, disjoint = set(), set()
for i, j in combinations(O, 2):
    if edge_count(O[i] & O[j]) != 1 or len(patterns[i]) != 2 or len(patterns[j]) != 2:
        continue
    H = patterns[i] | patterns[j]
    cols = Counter(x[2] for x in H)
    if len(H) == 3:
        assert sorted(cols.values()) == [1, 2]
        overlap.add(canonical_pair(i, j))
    elif sorted(cols.values()) == [1, 1, 2]:
        disjoint.add(canonical_pair(i, j))
assert overlap == {canonical_pair(65, 73)}
assert disjoint == {canonical_pair(65, 70), canonical_pair(61, 65), canonical_pair(71, 73)}
stats['nonneighbour_normal_forms'] = 4

# Overlap: the two doubled pairs fill any four of the specified five
# positions; every C avoiding the rectangle-closing edge enables one
# of the two stated completions.
P, Q = 65, 73
for C in O:
    if C in (P, Q) or c('13') in O[C]:
        continue
    enabled = False
    for edge, T, ab, E in [
        ('04', 63, corners('03', '04'), corners('23', '32', '24', '42', '30')),
        ('14', 68, corners('03', '14'), corners('01', '10', '30', '34', '43')),
    ]:
        if c(edge) not in O[C]:
            continue
        enabled = True
        assert ab == A & O[T]
        assert O[T] - ab - {rev(c(edge))} == E
        pairs = [O[P], O[P], O[Q], O[Q]]
        assert all(matched(pairs, ps) for ps in combinations(E, 4))
        check_rescue(E)
        for B in m.CUTS:
            if B & E:
                assert matched(pairs + [O[C], A, A, B], O[T])
                stats['overlap_helper_checks'] += 1
    assert enabled

# Disjoint: verify both explicit completions and each rescue set.
rows = [
    (65, 70, 63, '24', '23', [63, 64, 73], '03', '04'),
    (61, 65, 68, '34', '01', [68, 71, 73], '14', '03'),
    (71, 73, 68, '01', '34', [61, 65, 68], '14', '03'),
]
for P, Q, T, d, e, cs, a, b in rows:
    H = patterns[P] | patterns[Q]
    assert sorted(i for i, p in patterns.items() if i not in (P, Q) and p <= H) == cs
    assert O[P] & O[Q] == bi(d)
    assert (A & O[T]) == corners(a, b)
    for C in cs:
        assert bi(e) <= O[C]
        assert corners(a, b) & O[C]
        for D, other, x in [(P, Q, a), (Q, P, b)]:
            if c(x) not in O[C]:
                continue
            E3 = O[D] - bi(d) - {rev(c(x))} - (A & O[D])
            assert len(E3) == 3
            E = E3 | bi(e)
            check_rescue(E)
            assert not (E & A)
            for B in m.CUTS:
                if not B & E:
                    continue
                src = [O[P], O[P], O[Q], O[Q], O[C], A, A, B]
                assert matched(src, O[T]) or matched(src, O[D])
                if B & bi(e):
                    assert matched(src, O[T])
                if B & E3:
                    assert matched(src, O[D])
                stats['disjoint_helper_checks'] += 1

out = {'status': 'passed', 'scope': 'small geometric normal forms and explicit assignments; no inventory exhaustion', 'checks': dict(stats)}
path = Path(__file__).with_name('five-target-audit.json')
path.write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
