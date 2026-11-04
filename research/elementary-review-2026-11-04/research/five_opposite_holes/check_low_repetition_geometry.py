"""Independent checks of the geometric assertions in the virtual-triple proof.

This is corroboration, not an inventory-enumeration premise in the proof.
It normalizes A=C(01), enumerates opposite profiles with at most one
doubled variety, and checks exactly the central-target consequence used.
"""
from itertools import combinations
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'root'))
from cut_model import CUTS, CORNERS

ADJ = list(CUTS)
OPP = list(CORNERS[60:])
A = ADJ[0]
E = [frozenset((a, b) if a < b else (b, a)
               for _, a, b in t) for t in OPP]


def matching(sources, positions):
    """Whether every requested position can be matched to a source."""
    owners = [-1] * len(sources)
    positions = list(positions)
    positions.sort(key=lambda p: sum(p in s for s in sources))

    def aug(k, seen):
        for i, s in enumerate(sources):
            if i in seen or positions[k] not in s:
                continue
            seen.add(i)
            if owners[i] < 0 or aug(owners[i], seen):
                owners[i] = k
                return True
        return False

    return all(aug(k, set()) for k in range(len(positions)))


def inventories():
    for x in combinations(range(15), 5):
        yield x
    for d in range(15):
        for x in combinations([v for v in range(15) if v != d], 3):
            yield (d, d) + x


counts = {'inventories': 0, 'rectangle_cases': 0,
          'central_cases': 0, 'central_witnesses': 0,
          'five_position_checks': 0, 'two_corner_patterns': 0}
for inv in inventories():
    counts['inventories'] += 1
    sources = [OPP[v] for v in inv]
    rectangles = [A & t for t in OPP if len(A & t) == 4]
    assert len(rectangles) == 3
    if any(matching(sources, r) for r in rectangles):
        counts['rectangle_cases'] += 1
        continue
    counts['central_cases'] += 1
    candidates = []
    for ti, t in enumerate(OPP):
        reserve = A & t
        if len(reserve) != 2:
            continue
        if not all(len(E[v] & E[ti]) >= 2 for v in inv):
            continue
        if not all(sum(e in E[v] for v in inv) >= 2 for e in E[ti]):
            continue
        doubled = next((v for v in inv if inv.count(v) == 2), None)
        if doubled is not None and doubled != ti and not (reserve - OPP[doubled]):
            continue
        candidates.append(ti)
        counts['central_witnesses'] += 1
        remaining = t - reserve
        assert len(remaining) == 6
        for hole in remaining:
            assert matching(sources, remaining - {hole}), (inv, ti, hole)
            counts['five_position_checks'] += 1
        trapped = [j for j, cut in enumerate(ADJ) if (cut & t) <= reserve]
        assert 0 in trapped and len(trapped) <= 2, (ti, trapped)
    assert candidates, inv

for t in OPP:
    for reserve in combinations(t, 2):
        reserve = frozenset(reserve)
        trapped = [j for j, cut in enumerate(ADJ) if (cut & t) <= reserve]
        assert len(trapped) <= 2
        counts['two_corner_patterns'] += 1

out = Path(__file__).with_name('low-repetition-geometry-audit.json')
out.write_text(json.dumps(counts, indent=2) + '\n')
print(json.dumps(counts, indent=2))
