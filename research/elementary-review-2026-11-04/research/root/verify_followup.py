#!/usr/bin/env python3
"""Independent finite checks of the small certificates in this follow-up.

These checks audit written arguments; they do not prove the outstanding
fourteen-cube exhaustion lemma. Standard library only. Run from the
archive root: python3 research/root/verify_followup.py
"""
from pathlib import Path
import itertools
import json
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from cut_model import CUTS, CORNERS, CLASSES, V, match_target


def counts(classes):
    x = [0] * 75
    for j, n in classes.items():
        x[3*j] = n
    return x


def check_nine_table():
    data = json.loads((HERE / 'nine-distinct-hall-certificate.json').read_text())
    feasible = templates = 0
    for row in data:
        core = set(row['core'])
        helpers = set(range(20)) - core
        assert len(core) == 5 and all(CLASSES[j][1] == 1 for j in core)
        for entry in row['targets']:
            target = sorted(CORNERS[entry['target']])
            certified = []
            for rec in entry['templates']:
                s = set(map(tuple, rec['corners']))
                assert s <= set(target)
                avoid = {j for j in helpers if not CUTS[j] & s}
                k = len(s)-1-sum(bool(CUTS[j] & s) for j in core)
                assert avoid == set(rec['avoid']) and k == rec['k']
                certified.append((avoid, k))
                templates += 1
            for n in range(1, 5):
                for cells in itertools.combinations(target, n):
                    s = set(cells)
                    k = n-1-sum(bool(CUTS[j] & s) for j in core)
                    avoid = {j for j in helpers if not CUTS[j] & s}
                    if k < 0 or len(avoid)+k < 4:
                        continue
                    feasible += 1
                    # Exact set-inclusion implication, without enumerating H.
                    assert any(len(avoid-b)+k <= l for b, l in certified)

        if row is data[0]:
            first, second, third = row['targets']
            # The special k=1 obstructions require class9, absent from
            # both first-target k=0 sets.
            assert all(9 not in r['avoid'] for r in first['templates'])
            for entry in (second, third):
                special = next(r for r in entry['templates'] if r['k'] == 1)
                assert len(special['avoid']) == 3 and 9 in special['avoid']
            b = set(next(r['avoid'] for r in second['templates'] if r['k'] == 0))
            c = set(next(r['avoid'] for r in third['templates'] if r['k'] == 0))
            assert all(len(set(a['avoid']) & b & c) <= 3
                       for a in first['templates'])
        else:
            first, second = row['targets']
            assert all(a['k'] == b['k'] == 0 and
                       len(set(a['avoid']) & set(b['avoid'])) <= 3
                       for a in first['templates'] for b in second['templates'])
    print(f'Nine-class certificate: {templates} templates cover {feasible} feasible small Hall sets.')


def check_corner_geometry():
    target = sorted(CORNERS[60])
    for n, bound in ((2, 2), (3, 3)):
        assert max(sum((c & set(target)) <= set(s) for c in CUTS)
                   for s in itertools.combinations(target, n)) <= bound
    a = CUTS[0]
    h = {('t', 0, 3), ('t', 0, 4), ('t', 1, 3)}
    assert {j for j, c in enumerate(CUTS) if not c & h} == {
        1, 3, 7, 9, 10, 14, 16, 18}
    for quad in ((1, 3, 7, 9), (10, 14, 16, 18)):
        for triple in itertools.combinations(quad, 3):
            x = counts({j: 2 for j in (0,) + triple})
            assert any(match_target(x, t) for t in range(60, 75))
    butterfly = (0, 2, 5, 7, 8, 19)
    union = set().union(*(CUTS[j] for j in butterfly))
    missing = {('t', q, p) for q in (3, 4) for p in (1, 2)}
    all_arcs = {('t', a, b) for a in V for b in V if a != b}
    assert all_arcs-union == missing
    for j in set(range(20))-set(butterfly):
        x = counts({k: 2 for k in (0, 2, 5, 7)})
        x[3*j] += 1
        assert any(match_target(x, t) for t in range(60, 75))
    print('Six-doubled-class geometry, eight short cores, and fourteen butterfly extensions: passed.')


def check_sharpness():
    data = json.loads((HERE / 'eight-distinct-class-counterexample.json').read_text())
    x = data['counts']
    assert sum(x) == 8
    assert sum(sum(x[3*j:3*j+3]) > 0 for j in range(20)) == 8
    assert not any(match_target(x, t) for t in range(75))
    sources = [i for i, n in enumerate(x) for _ in range(n)]
    union = set().union(*(CORNERS[i] for i in sources))
    supported = {t for t in range(75) if CORNERS[t] <= union}
    assert supported == {r['target'] for r in data['hall_certificates']}
    for r in data['hall_certificates']:
        s = set(map(tuple, r['S']))
        assert s <= CORNERS[r['target']]
        neighbours = [i for i in sources if CORNERS[i] & s]
        assert neighbours == r['N'] and len(neighbours) < len(s)
    print('Sharpness: eight distinct classes fail all75 targets; all14 supported targets have Hall certificates.')


if __name__ == '__main__':
    check_corner_geometry()
    check_nine_table()
    check_sharpness()
    print('The global exhaustion lemma remains unproved.')
