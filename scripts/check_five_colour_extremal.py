#!/usr/bin/env python3
"""Check the proposed compact (4,5,5) classification and mixed family.

Uses the committed, previously audited physical incidence table. The orbit
action is constructed directly from all colour permutations, reflections,
and proper rotations. The 91-member family is also checked by actual-copy
augmenting-path matching. This is an audit, not a Lean proof.
"""
import argparse
from collections import Counter
import itertools
import json
from pathlib import Path
import subprocess
import time


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--repo', type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument('--output', type=Path, default=Path(__file__).resolve().parents[1] / 'build/checks/extremal.json')
    args = ap.parse_args()
    start = time.monotonic()
    repo = args.repo.resolve()
    lines = (repo / 'data/five-colour-geometry.txt').read_text().splitlines()
    faces = [tuple(map(int, line.split())) for line in lines[1:76]]
    geometry = [list(map(int, line.split())) for line in lines[76:]]
    require(int(lines[0]) == 75 and len(faces) == len(geometry) == 75, 'catalogue dimensions')

    def target_solves(a, b, c, t):
        x, y, z = (geometry[t][i] for i in (a, b, c))
        return ((x | y | z) == 255 and
                (x & ~(y | z)).bit_count() <= 4 and
                (y & ~(x | z)).bit_count() <= 5 and
                (z & ~(x | y)).bit_count() <= 5)

    failures, necessary = set(), []
    checked = 0
    for a in range(75):
        for b, c in itertools.combinations([i for i in range(75) if i != a], 2):
            checked += 1
            if any(target_solves(a, b, c, t) for t in (a, b, c)):
                continue
            if geometry[a][b] and geometry[a][c] and geometry[b][c]:
                necessary.append((a, b, c))
            if not any(target_solves(a, b, c, t) for t in range(75)):
                failures.add((a, b, c))
    require(checked == 202575 and len(failures) == 840 and len(necessary) == 900,
            'unexpected classification counts')

    directions = [(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]
    rotations = []
    for p in itertools.permutations(range(3)):
        parity = (-1) ** sum(p[i] > p[j] for i in range(3) for j in range(i+1, 3))
        for signs in itertools.product((-1, 1), repeat=3):
            if parity * signs[0] * signs[1] * signs[2] != 1:
                continue
            rotations.append(tuple(directions.index(tuple(signs[j] * v[p[j]] for j in range(3)))
                                   for v in directions))
    require(len(set(rotations)) == 24, 'proper rotation group')
    def canonical(f):
        return min(tuple(f[j] for j in r) for r in rotations)
    lookup = {canonical(f): i for i, f in enumerate(faces)}
    require(len(lookup) == 75, 'distinct physical varieties')
    a = lookup[canonical((0,0,1,2,3,4))]
    bs = {2: lookup[canonical((0,1,2,3,2,4))],
          3: lookup[canonical((0,1,2,3,3,4))],
          4: lookup[canonical((0,1,2,4,3,4))]}
    cs = {1: lookup[canonical((0,3,1,2,4,1))],
          2: lookup[canonical((0,3,1,2,4,2))],
          4: lookup[canonical((0,3,1,4,4,2))]}
    def arcs(f):
        result = set()
        for signs in itertools.product((0,1), repeat=3):
            values = tuple(f[2*i+signs[i]] for i in range(3))
            if len(set(values)) != 3:
                continue
            if sum(signs) % 2:
                values = (values[0],values[2],values[1])
            u,v = sorted(set(range(5))-set(values))
            order = (u,v,*values)
            odd = sum(order[i]>order[j] for i in range(5) for j in range(i+1,5)) % 2
            result.add((v,u) if odd else (u,v))
        return result
    cut = lambda s: {(u,v) for u in s for v in set(range(5))-set(s)}
    require(all(arcs(faces[i]) == cut({0,1}) for i in bs.values()), 'B directed-cut dictionary')
    require(all(arcs(faces[i]) == cut({1,2,4}) for i in cs.values()), 'C directed-cut dictionary')
    require(arcs(faces[a]) == {(u,v) for u in (1,2) for v in (3,4)} |
            {(v,u) for u in (1,2) for v in (3,4)}, 'opposite anchor dictionary')
    representatives = [(2,1),(2,4),(3,1),(3,2),(4,2)]
    all_orbits, orbits = set(), []
    for r, s in representatives:
        orbit = set()
        for colour_map in itertools.permutations(range(5)):
            for reflected in (False, True):
                mapped = []
                for i in (a, bs[r], cs[s]):
                    f = tuple(colour_map[k] for k in faces[i])
                    if reflected:
                        f = (f[1], f[0], *f[2:])
                    mapped.append(lookup[canonical(f)])
                orbit.add((mapped[0], *sorted(mapped[1:])))
        require(orbit <= failures, 'representative orbit contains a solution')
        require(not (all_orbits & orbit), 'representatives are equivalent')
        all_orbits |= orbit
        orbits.append({'repeated_colours': [r, s], 'size': len(orbit)})
    require(all_orbits == failures, 'five orbits do not exhaust failures')
    require([o['size'] for o in orbits] == [240,120,120,240,120], 'unexpected orbit sizes')

    def copy_match(ids, target):
        match = [-1] * len(ids)
        def augment(k, seen):
            for j, i in enumerate(ids):
                if j in seen or not (geometry[target][i] >> k & 1):
                    continue
                seen.add(j)
                if match[j] == -1 or augment(match[j], seen):
                    match[j] = k
                    return True
            return False
        return all(augment(k, set()) for k in range(8))

    for a0,b0,c0 in failures:
        require(not any(copy_match([a0]*4+[b0]*5+[c0]*5, t) for t in range(75)),
                'private-position failure disagrees with physical-copy matching')
    dictionary = json.loads((repo / 'data/five-colour-extremal.json').read_text())
    require(dictionary['anchor']['faces'] == list(faces[a]), 'anchor face dictionary')
    for label,group in [('B',bs),('C',cs)]:
        for r,i in group.items():
            require(dictionary[label][str(r)]['faces'] == list(faces[i]) and
                    dictionary[label][str(r)]['catalogue_index'] == i, 'face dictionary')
    require([entry['labelled_orbit_size'] for entry in dictionary['classes']] ==
            [entry['size'] for entry in orbits], 'orbit-size dictionary')
    parts = [(x, y, 5-x-y) for x in range(6) for y in range(6-x)]
    family = []
    for x, y in itertools.product(parts, repeat=2):
        if x[0] * y[1] or x[2] * y[2]:
            continue
        ids = [a] * 4
        for i, n in zip([bs[2],bs[3],bs[4],cs[1],cs[2],cs[4]], x+y):
            ids.extend([i] * n)
        require(not any(copy_match(ids, target) for target in range(75)), 'mixed family has a solution')
        family.append({'x': x, 'y': y})
    require(len(family) == 91, 'mixed-family count')
    is_opposite = lambda i: any(faces[i][j] == faces[i][j+1] for j in (0,2,4))
    kinds = Counter(''.join('O' if is_opposite(i) else 'A' for i in t) for t in necessary)
    git = subprocess.run(['git','-C',str(repo),'rev-parse','HEAD'], capture_output=True, text=True)
    result = {
        'status': 'computational audit passed; not a Lean proof',
        'commit': git.stdout.strip() if git.returncode == 0 else None,
        'pattern': [4,5,5], 'collections_checked': checked,
        'necessary_condition_candidates': len(necessary), 'candidate_types': dict(kinds),
        'failures': len(failures), 'orbits': orbits,
        'orbit_union_equals_exact_failure_set': True,
        'failure_set': sorted(failures),
        'mixed_family_count': len(family),
        'mixed_family_support_counts': dict(Counter(1+sum(v>0 for v in q['x']+q['y']) for q in family)),
        'mixed_family_max_multiplicity_counts': dict(Counter(max(4,*q['x'],*q['y']) for q in family)),
        'mixed_family': family, 'seconds': round(time.monotonic()-start, 3),
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('failure_set','mixed_family')}, indent=2))


if __name__ == '__main__':
    main()
