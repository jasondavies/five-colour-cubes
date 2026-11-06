#!/usr/bin/env python3
"""Independent physical audit of the 56 obstruction representatives.

Reconstructs proper rotations, the catalogue, physical compatibility, and all
colour/reflection actions without importing production geometry or matching.
This validates failures and orbit data; exhaustive coverage is certified by
Q5E1 replay and its Lean physical-root bridge, not by this example audit.
"""
import argparse
from collections import Counter
import itertools
import json
from pathlib import Path
import time


def require(ok, message):
    if not ok:
        raise ValueError(message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument('--dictionary', type=Path)
    args = parser.parse_args()
    repo = args.repo.resolve()
    started = time.monotonic()
    rotations = {tuple(range(6))}
    pending = list(rotations)
    while pending:
        p = pending.pop()
        for q in ((0, 1, 5, 4, 2, 3), (3, 2, 0, 1, 4, 5)):
            r = tuple(p[i] for i in q)
            if r not in rotations:
                rotations.add(r)
                pending.append(r)
    require(len(rotations) == 24, 'proper rotation group')
    def canonical(f):
        return min(tuple(f[i] for i in r) for r in rotations)
    faces = sorted({canonical(f) for f in itertools.product(range(5), repeat=6)
                    if len(set(f)) == 5})
    require(len(faces) == 75, 'catalogue size')
    slots = [(i, 2+j, 4+k) for i, j, k in itertools.product(range(2), repeat=3)]
    fits = [[sum(1 << k for k, slot in enumerate(slots)
                 if any(all(source[r[a]] == target[a] for a in slot) for r in rotations))
             for source in faces] for target in faces]
    raw = list(map(int, (repo/'data/five-colour-geometry.txt').read_text().split()))
    require(raw == [75] + [c for f in faces for c in f] + [m for row in fits for m in row],
            'physical geometry disagrees with retained incidence data')
    lookup = {f: i for i, f in enumerate(faces)}
    actions = []
    for p in itertools.permutations(range(5)):
        for reflected in (False, True):
            action = []
            for f in faces:
                g = tuple(p[c] for c in f)
                if reflected:
                    g = (g[1], g[0], *g[2:])
                action.append(lookup[canonical(g)])
            actions.append(action)
    require(len(set(map(tuple, actions))) == 240, 'global symmetry actions')
    data = json.loads((args.dictionary or repo/'data/five-colour-classification.json').read_text())
    require(data['format'] == 1 and len(data['representatives']) == 56, 'classification schema')
    labelled, by_support, by_form = set(), Counter(), Counter()
    form_orbits = {name: set() for name in ['generalized', 'adjacent', 'exceptional']}
    for j, entry in enumerate(data['representatives']):
        v = entry['varieties']
        require(len(v) == 14 and all(type(i) is int and 0 <= i < 75 for i in v), 'physical inventory')
        require(len(entry['hall_masks']) == 75, 'missing target deficiencies')
        for t, d in enumerate(entry['hall_masks']):
            require(type(d) is int and 0 < d < 256, 'invalid Hall mask')
            require(sum(bool(fits[t][i] & d) for i in v) < d.bit_count(),
                    f'false Hall deficiency: representative {j}, target {t}')
            owner = [-1]*14
            def augment(k, seen):
                for q, i in enumerate(v):
                    if q in seen or not (fits[t][i] >> k & 1):
                        continue
                    seen.add(q)
                    if owner[q] < 0 or augment(owner[q], seen):
                        owner[q] = k
                        return True
                return False
            require(not all(augment(k, set()) for k in range(8)), 'representative assembles')
        orbit = {tuple(sorted(a[i] for i in v)) for a in actions}
        require(len(orbit) == entry['orbit_size'], 'incorrect orbit size')
        require(not labelled & orbit, 'equivalent representatives')
        labelled.update(orbit)
        require(entry['form'] in form_orbits, 'unknown structural form')
        form_orbits[entry['form']].update(orbit)
        by_support[len(set(v))] += len(orbit)
        by_form[entry['form']] += len(orbit)
        opposite = sum(faces[i][a] == faces[i][a+1] for i in v for a in (0, 2, 4))
        require((entry['form'] == 'adjacent') == (opposite == 0), 'incorrect all-adjacent form')
    require(len(labelled) == 11430, 'labelled census')
    require(by_support == {3: 840, 4: 4800, 5: 5280, 6: 510}, 'support census')
    require(by_form == {'generalized': 10920, 'adjacent': 270, 'exceptional': 240}, 'form census')
    # Reconstruct the three mathematical normal forms, independently of the
    # representative list and its form labels.
    def arcs(f):
        result = set()
        for signs in itertools.product((0, 1), repeat=3):
            triple = tuple(f[2*i+signs[i]] for i in range(3))
            if len(set(triple)) < 3:
                continue
            if sum(signs) % 2:
                triple = (triple[0], triple[2], triple[1])
            a, b = sorted(set(range(5))-set(triple))
            order = (a, b, *triple)
            odd = sum(order[i] > order[j] for i in range(5) for j in range(i+1, 5)) % 2
            result.add((b, a) if odd else (a, b))
        return frozenset(result)
    adjacent = {(arcs(f), next(c for c, n in Counter(f).items() if n == 2)): i
                for i, f in enumerate(faces) if not any(f[a] == f[a+1] for a in (0, 2, 4))}
    require(len(adjacent) == 60, 'directed-cut dictionary')
    def cut(s):
        return frozenset((a, b) for a in s for b in set(range(5))-set(s))
    def all_images(seeds):
        return {tuple(sorted(a[i] for i in v)) for v in seeds for a in actions}
    compositions = [(x, y, 5-x-y) for x in range(6) for y in range(6-x)]
    normal = []
    anchor = lookup[canonical((0, 0, 1, 2, 3, 4))]
    for x, y in itertools.product(compositions, repeat=2):
        if x[0]*y[1] or x[2]*y[2]:
            continue
        v = [anchor]*4
        for counts, repeats, side in [(x, (2, 3, 4), {0, 1}), (y, (1, 2, 4), {1, 2, 4})]:
            for n, r in zip(counts, repeats):
                v += [adjacent[cut(side), r]]*n
        normal.append(v)
    require(len(normal) == 91 and all_images(normal) == form_orbits['generalized'],
            'generalized normal form does not match its advertised classes')
    normal = []
    for values in itertools.permutations(range(4)):
        if any(i == values[i] for i in range(4)):
            continue
        v = [adjacent[cut({0, 3}), 4], adjacent[cut({0, 3, 4}), 4]]
        for i in range(4):
            side = {i, 4} if i in (0, 3) else set(range(5))-{i, 4}
            v += [adjacent[cut(side), values[i]]]*3
        normal.append(v)
    require(len(normal) == 9 and all_images(normal) == form_orbits['adjacent'],
            'derangement normal form does not match its advertised classes')
    exception = [(5, (0, 1, 0, 2, 3, 4)), (1, (0, 4, 1, 2, 3, 1)),
                 (1, (0, 4, 1, 2, 3, 2)), (1, (0, 4, 1, 3, 3, 2)),
                 (3, (0, 4, 1, 2, 3, 3)), (3, (0, 4, 1, 4, 3, 2))]
    v = [lookup[canonical(f)] for n, f in exception for _ in range(n)]
    require(all_images([v]) == form_orbits['exceptional'], 'mixed normal form mismatch')
    terminals = [tuple(v) for v in data['terminals']]
    require(len(set(terminals)) == len(terminals) == 81, 'terminal inventory list')
    require(all(tuple(sorted(v)) in labelled for v in terminals), 'terminal outside representatives')
    require(set(j for r in data['roots'] for j in r['terminals']) == set(range(81)),
            'root terminal coverage')
    print(f'Physical classification audit passed: 56 inequivalent failures, 11,430 labelled inventories, '
          f'81 terminals; {time.monotonic()-started:.2f}s.')

if __name__ == '__main__':
    main()
