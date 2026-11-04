#!/usr/bin/env python3
"""Audit the alternative distinct-case split using physical quarter turns.

This checks geometry and coverage, not the C++ exhaustive-search implementation.
It imports no search-model or case-generator code.
"""
from collections import Counter
import itertools
import json
from pathlib import Path
from physical_geometry import canonical, corner_types, fits, match, require

OUT = Path(__file__).resolve().parents[1] / 'data'
REPORT = Path(__file__).resolve().parents[1] / 'build/checks'
REPORT.mkdir(parents=True, exist_ok=True)


def main(geometry=None):
    if geometry is None:
        from check_five_colour import main as audit_geometry
        geometry = audit_geometry()
    cubes, slots, masks = geometry
    index = {c: i for i, c in enumerate(cubes)}
    opposite = [any(c[2*j] == c[2*j+1] for j in range(3)) for c in cubes]
    anchors = [opposite.index(False), opposite.index(True)]
    doubles = [{q for q in corner_types(c) if len(set(q)) == 2} for c in cubes]
    require(len(set().union(*doubles)) == 20, 'Double-corner palette')
    require(all(len(d) == (0 if o else 2) for d, o in zip(doubles, opposite)),
            'Double-corner incidence count')
    raw = (OUT / 'q5-distinct-shared-cases-size15.txt').read_text().splitlines()
    rows = [list(map(int, row.split())) for row in raw[1:]]
    require(len(rows) == int(raw[0]) == 113, 'Wrong case count')
    for kind, anchor in enumerate(anchors):
        group = []
        orbit = set()
        for p in itertools.permutations(range(5)):
            for mirror in (False, True):
                def image(c):
                    d = tuple(p[a] for a in c)
                    if mirror:
                        d = (d[1], d[0], *d[2:])
                    return index[canonical(d)]
                orbit.add(image(cubes[anchor]))
                if image(cubes[anchor]) == anchor:
                    group.append([image(c) for c in cubes])
        require(orbit == {i for i, o in enumerate(opposite) if o == bool(kind)},
                'Incomplete anchor orbit')
        characteristic = sum(1 << k for k, q in enumerate(corner_types(cubes[anchor]))
                             if len(set(q)) == 2)
        represented = set()
        for row in rows:
            if row[0] != kind:
                continue
            _, m, k, size, a, budget, *rest = row
            require((m, size, a) == (1, 15, anchor), 'Wrong anchor')
            require(kind == 1 or k != 255 ^ characteristic, 'Excluded cut retained')
            bad = [int(i != anchor and bool(mask & ~k))
                   for i, mask in enumerate(masks[anchor])]
            require(budget == 6 - k.bit_count() >= 0 and rest[75:] == bad,
                    'Wrong Hall cut')
            caps = [int(kind == 1 or not o) for o in opposite]
            for i in range(75):
                if bad[i]:
                    caps[i] = min(caps[i], budget)
            caps[anchor] = 0
            require(rest[:75] == caps, 'Wrong root capacities')
            represented.add((sum(b << i for i, b in enumerate(bad)), budget))
        for k in range(256):
            if k.bit_count() > 6 or (kind == 0 and k == 255 ^ characteristic):
                continue
            bad = [i for i, mask in enumerate(masks[anchor]) if i != anchor and mask & ~k]
            require(any((sum(1 << p[i] for i in bad), 6-k.bit_count()) in represented
                        for p in group), 'Missing cover orbit')
    # Normalize the known solution-free eleven-set, then check that a case
    # actually contains it. This catches accidental pruning of all obstructions.
    witness = json.loads((OUT / 'q5-local-distinct.json').read_text())
    ids = [index[canonical(tuple(e['faces']))] for e in witness['collection']]
    require(len(ids) == len(set(ids)) == 11, 'Bad eleven-set witness')
    source = next(i for i in ids if opposite[i])
    counts = [int(i in ids) for i in range(75)]
    require(not any(match(s, counts) for s in slots), 'Control is solvable')
    control = None
    for p in itertools.permutations(range(5)):
        for mirror in (False, True):
            def image(c):
                d = tuple(p[a] for a in c)
                if mirror:
                    d = (d[1], d[0], *d[2:])
                return index[canonical(d)]
            if image(cubes[source]) != anchors[1]:
                continue
            normalized = {image(cubes[i]) for i in ids}
            for row in rows:
                if row[0] != 1:
                    continue
                rest = normalized - {row[4]}
                if all(row[6+i] for i in rest) and sum(row[81+i] for i in rest) <= row[5]:
                    control = row.copy()
                    control[3] = 11
                    break
            if control is not None:
                break
        if control is not None:
            break
    require(control is not None, 'Known obstruction excluded by partition')
    require((OUT / 'q5-distinct-known-control.txt').read_text() ==
            '1\n' + ' '.join(map(str, control)) + '\n', 'Control fixture differs')
    result = dict(case_count=len(rows), case_counts=dict(Counter(r[0] for r in rows)),
                  physical_cover_audit=True, double_corner_types=20,
                  known_obstruction_covered=True, known_obstruction_cover=control[2])
    (REPORT / 'q5-distinct-independent-check.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
