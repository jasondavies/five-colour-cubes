"""Small independent audits for the second elementary-proof follow-up.

These check the finite geometry and displayed constructions used in the
written proofs. They do not assume or enumerate the fourteen-failure list.
Run from any directory with standard-library Python.
"""

from itertools import combinations, product
from cut_model import V, CLASSES, CUTS, CORNERS, OPP, solution


def arc(s):
    return ('t', int(s[0]), int(s[1]))


def arcs(*ss):
    return frozenset(map(arc, ss))


LABEL = {
    ''.join(map(str, p if sign == 1 else [v for v in V if v not in p])): j
    for j, (p, sign) in enumerate(CLASSES)
}


def cut(label):
    return CUTS[LABEL[label]]


def opposite(p, q):
    return frozenset(('t', a, b) for aa, bb in ((p, q), (q, p))
                     for a in aa for b in bb)


def match(positions, source_sets):
    owner = [None] * len(source_sets)

    def augment(c, seen):
        for i, ss in enumerate(source_sets):
            if i in seen or c not in ss:
                continue
            seen.add(i)
            if owner[i] is None or augment(owner[i], seen):
                owner[i] = c
                return True
        return False

    return all(augment(c, set()) for c in positions)


def assignment(p, q, sources):
    occupied = []
    for label, corners in sources.items():
        assigned = [arc(c) for c in corners]
        assert set(assigned) <= cut(label), (label, corners)
        occupied.extend(assigned)
    assert len(occupied) == 8 and len(set(occupied)) == 8
    assert set(occupied) == opposite(p, q)


def column_geometry():
    private = arcs('02', '12')
    allowed = {'01'} | {name for name in LABEL
                         if not cut(name) & private}
    assert allowed == {
        '01', '02', '12', '123', '124', '023', '024', '012',
        '234', '23', '24', '34'
    }
    rows = [arcs('20', '21'), arcs('30', '31'), arcs('40', '41')]
    reverse = frozenset.union(*rows)
    expected = {
        '02': arcs('21'), '12': arcs('20'),
        '123': arcs('20', '30'), '124': arcs('20', '40'),
        '023': arcs('21', '31'), '024': arcs('21', '41'),
        '012': frozenset(), '234': reverse,
        '23': rows[0] | rows[1], '24': rows[0] | rows[2],
        '34': rows[1] | rows[2],
    }
    assert all(cut(name) & reverse == value
               for name, value in expected.items())

    def restricted(anchor, ss):
        return {name for name in allowed
                if name == anchor or not cut(name) & ss}

    assert restricted('012', arcs('23', '24')) == {'01', '012', '234', '34'}
    assert restricted('02', arcs('01', '21')) == {
        '01', '02', '12', '123', '124', '34', '012'}
    assert restricted('123', arcs('20', '24')) == {'01', '123', '024', '34'}
    assert restricted('123', arcs('30', '34')) == {
        '01', '123', '02', '12', '124', '024', '24', '012'}
    assert restricted('23', arcs('20', '30')) == {'01', '23', '02', '023', '024', '012'}
    assert restricted('23', arcs('24', '34')) == {'01', '23', '234', '124', '024', '24', '34'}

    nonempty = {name: value for name, value in expected.items() if value}
    for n in range(5):
        for ss in combinations(reverse, n):
            ss = frozenset(ss)
            contained = {name for name, value in nonempty.items() if value <= ss}
            if n <= 3:
                assert len(contained) <= n
            elif len(contained) >= 5:
                assert ss in (rows[0] | rows[1], rows[0] | rows[2])
                assert len(contained) == 5

    # Section 5's scalar Hall reduction, with all six counts at most two.
    for p, q, v, x, z, h in product(range(3), repeat=6):
        if p + q + v + x + z + h != 8:
            continue
        sources = ([arcs('21')] * p + [arcs('40')] * v
                   + [arcs('21', '41')] * x + [arcs('21', '40', '41')] * z)
        if v + z and x + z:
            assert match(arcs('21', '40', '41'), sources)
        elif x != 0:
            assert z == v == 0 and p == q == x == h == 2

    assignment((0, 4), (1, 3), {
        '01': ['03', '14'], '123': ['10', '30', '34'],
        '024': ['01', '41', '43'],
    })
    family = ['01', '02', '12', '123', '124', '012']
    union = frozenset.union(*(cut(name) for name in family))
    all_arcs = frozenset(('t', a, b) for a in V for b in V if a != b)
    assert all_arcs - union == arcs('31', '32', '41', '42')
    assert not any(target <= union for target in CORNERS[60:])
    print('Private-column geometry, cover bounds, Hall reduction and butterfly support: passed.')


def own_loop_constructions():
    assignment((0, 4), (2, 3), {
        '01': ['02'], '014': ['03', '42', '43'],
        '123': ['30', '34'], '24': ['20'], '012': ['24'],
    })
    assignment((1, 3), (2, 4), {
        '01': ['12', '14'], '013': ['32'], '123': ['34'],
        '014': ['43'], '24': ['21', '23', '41'],
    })
    assignment((1, 3), (2, 4), {
        '01': ['12', '14'], '013': ['32'], '123': ['34'],
        '014': ['43'], '24': ['21', '23'], '04': ['41'],
    })
    print('Two-own-loop-triple opposite constructions: passed.')


def sharpness():
    counts = [0] * 75
    entries = [('01', 2, 3), ('02', 1, 3), ('124', 4, 3),
               ('123', 3, 3), ('12', 0, 1), ('012', 0, 1)]
    for label, repeat, number in entries:
        j = LABEL[label]
        repeats = [v for v in V if v not in CLASSES[j][0]]
        counts[3 * j + repeats.index(repeat)] = number
    assert sum(counts) == 14
    assert solution(counts) is None
    print('Fourteen-cube all-adjacent sharpness example, all75 targets: passed.')


def rescue_geometry():
    edges = [frozenset(e) for e in combinations(V, 2)]
    cycles = [{frozenset((a, b)) for _, a, b in cc} for cc in CORNERS[60:]]
    assert all(sum(e in cc for cc in cycles) == 6 for e in edges)
    for e, f in combinations(edges, 2):
        avoiding = [i for i, cc in enumerate(cycles) if not cc & {e, f}]
        assert len(avoiding) == 5
        forbidden = frozenset(('t', a, b) for edge in (e, f)
                              for a in edge for b in edge if a != b)
        cut_avoiders = [j for j, cc in enumerate(CUTS) if not cc & forbidden]
        assert len(cut_avoiders) == (2 if e & f else 4)
        if e & f:
            assert CLASSES[cut_avoiders[0]][0] == CLASSES[cut_avoiders[1]][0]

    for forbidden, target in [([(0, 1), (0, 2)], 0), ([(0, 1), (2, 3)], 12)]:
        forbidden = set(map(frozenset, forbidden))
        pool = [CORNERS[60 + i] for i, cc in enumerate(cycles) if not cc & forbidden]
        assert len(pool) == 5
        for five in combinations(CORNERS[60 + target], 5):
            assert match(five, pool)

    P, Q, companion = 0, 7, 12
    remaining = [i for i in range(15) if i not in (P, Q, companion)]
    for s, u in combinations(remaining, 2):
        pool = [CORNERS[60 + i] for i in [P, P, Q, Q, companion, s, u]]
        rescue = set()
        for target in (2, 6):
            tt = CORNERS[60 + target]
            holes = {c for c in tt if match(tt - {c}, pool)}
            assert holes
            rescue.update(frozenset((a, b)) for _, a, b in holes)
        assert len(rescue) >= 2
    print('Rescue-edge geometry, five-variety cores and companion targets: passed.')


def six_source_path_geometry():
    cases = [
        ((0, 3), [(0, 2), (1, 2)], [4, 3, 3, 4]),
        ((0, 2), [(0, 3), (2, 1)], [4, 2, 2, 4]),
    ]
    for zero, other, expected in cases:
        actual = []
        for signs in product((0, 1), repeat=2):
            forbidden = {('t', *zero), ('t', *zero[::-1])}
            forbidden.update(('t', *(e if s == 0 else e[::-1]))
                             for e, s in zip(other, signs))
            actual.append(sum(not cc & forbidden for cc in CUTS))
        assert actual == expected
    t = CORNERS[60]
    for sources, holes in [
        ({'124': ['13', '23'], '12': ['14', '24'],
          '023': ['31'], '24': ['41']}, ['32', '42']),
        ({'134': ['32', '42'], '13': ['14'], '14': ['13'],
          '34': ['31', '41']}, ['23', '24']),
    ]:
        occupied = [arc(c) for c in holes]
        assert set(occupied) <= t
        for label, ss in sources.items():
            assert len(ss) <= 2 and arcs(*ss) <= cut(label)
            occupied.extend(arc(c) for c in ss)
        assert len(occupied) == len(set(occupied)) == 8
        assert set(occupied) == t
    print('Six-opposite path restrictions and both final assemblies: passed.')


if __name__ == '__main__':
    column_geometry()
    own_loop_constructions()
    sharpness()
    rescue_geometry()
    six_source_path_geometry()
    print('These audits do not claim the remaining mixed exhaustion lemma.')
