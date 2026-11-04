"""Check the explicit matchings in common-corner-eleven-hand.md.

This checks displayed geometric witnesses, not a source-inventory search.
"""
from collections import Counter
from itertools import permutations
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'root'))
from cut_model import CUTS, CLASSES, V


def cut_index(outset):
    outset = set(outset)
    corners = frozenset(('t', a, b) for a in outset for b in V if b not in outset)
    return CUTS.index(corners)


checks = []


def check(label, counts, reserve, target, assignments):
    left = Counter(counts)
    for source in reserve:
        left[source] -= 1
    assert min(left.values()) >= 0, label
    used = Counter(source for source, _ in assignments)
    assert all(n <= left[source] for source, n in used.items()), (label, used, left)
    corners = [('t', a, b) for _, (a, b) in assignments]
    assert len(corners) == len(set(corners)) == 6, (label, corners)
    assert frozenset(corners) == CUTS[target], (label, target, corners)
    assert all(corner in CUTS[source] for (source, _), corner in zip(assignments, corners)), label
    if reserve[0] != reserve[1]:
        p, q = CLASSES[target][0]
        x, y = (set(CLASSES[source][0]) for source in reserve)
        assert (p in x and q in y) or (q in x and p in y), label
    else:
        assert CLASSES[target][0] == CLASSES[reserve[0]][0], label
    checks.append(label)


for i, j, k in permutations((2, 3, 4)):
    A, B, C = (cut_index((0, q)) for q in (i, j, k))
    E, F = cut_index((0, i, k)), cut_index((0, i, j))
    family = {'A': A, 'B': B, 'C': C, 'E': E, 'F': F}
    for pattern in ('ABC', 'ABE', 'ABF', 'AEF', 'BCE', 'BEF'):
        counts = Counter({source: 3 if name in pattern else 1 for name, source in family.items()})
        prefix = f'{i}{j}{k}/{pattern}'
        if 'A' in pattern:
            assignments = [(A, (i, 1)), (E, (i, j)), (F, (i, k)), (B, (0, k)), (C, (0, j))]
            used = Counter(source for source, _ in assignments)
            helper = next(s for s in (B, C, E, F) if used[s] < counts[s])
            check(prefix + '/loopA', counts, (A, A), A, assignments + [(helper, (0, 1))])
        if pattern in ('ABF', 'BEF'):
            check(prefix + '/loopB', counts, (B, B), B,
                  [(B, (j, i)), (F, (j, 1)), (F, (j, k)), (A, (0, k)), (C, (0, i)), (E, (0, 1))])
        if pattern == 'BCE':
            check(prefix + '/loopC', counts, (C, C), C,
                  [(C, (k, i)), (E, (k, 1)), (E, (k, j)), (A, (0, j)), (B, (0, i)), (F, (0, 1))])
        if pattern in ('ABE', 'AEF'):
            check(prefix + '/loopE', counts, (E, E), E,
                  [(E, (k, 1)), (C, (k, j)), (A, (0, j)), (A, (i, j)), (F, (i, 1)), (B, (0, 1))])
        if pattern == 'BCE':
            check(prefix + '/loopE', counts, (E, E), E,
                  [(E, (i, 1)), (A, (i, j)), (C, (0, j)), (C, (k, 1)), (C, (k, j)), (B, (0, 1))])
        if pattern == 'BEF':
            check(prefix + '/loopF', counts, (F, F), F,
                  [(F, (i, 1)), (A, (i, k)), (B, (0, k)), (B, (j, 1)), (B, (j, k)), (C, (0, 1))])
        if pattern == 'ABC':
            check(prefix + '/edgeBC', counts, (B, C), B,
                  [(B, (j, i)), (B, (j, 1)), (F, (j, k)), (A, (0, k)), (A, (0, 1)), (C, (0, i))])
        if pattern in ('ABE', 'AEF'):
            pool = [s for s in (B, F) for _ in range(counts[s] - (s == B))]
            check(prefix + '/edgeAE', counts, (A, E), B,
                  [(A, (0, 1)), (A, (0, k)), (C, (0, i)), (B, (j, i)), (pool[0], (j, 1)), (pool[1], (j, k))])
        if pattern == 'BCE':
            check(prefix + '/edgeCE', counts, (C, E), B,
                  [(B, (j, i)), (B, (j, 1)), (B, (j, k)), (C, (0, 1)), (C, (0, i)), (A, (0, k))])
        if pattern == 'BEF':
            check(prefix + '/edgeBF', counts, (B, F), C,
                  [(E, (0, j)), (E, (k, 1)), (E, (k, j)), (B, (0, 1)), (B, (0, i)), (C, (k, i))])


P = {q: cut_index((0, q)) for q in (2, 3, 4)}
D = {q: cut_index({0, 2, 3, 4} - {q}) for q in (2, 3, 4)}
check('3332/support1', Counter({P[4]: 2, D[2]: 3, D[3]: 2, D[4]: 2}), (D[2], D[2]), D[2],
      [(D[2], (3, 2)), (P[4], (0, 2)), (P[4], (4, 2)), (D[4], (3, 1)), (D[3], (4, 1)), (D[3], (0, 1))])
check('3332/support2', Counter({P[3]: 3, P[4]: 2, D[3]: 2, D[4]: 3}), (P[3], P[3]), P[3],
      [(P[3], (3, 2)), (D[4], (0, 4)), (D[4], (3, 1)), (D[4], (3, 4)), (P[4], (0, 2)), (D[3], (0, 1))])
counts = Counter({P[3]: 2, P[4]: 2, D[2]: 2, D[4]: 2})
check('3332/support3/loopP3', counts, (P[3], P[3]), P[3],
      [(P[4], (0, 1)), (P[4], (0, 2)), (D[2], (3, 1)), (D[2], (3, 2)), (D[4], (0, 4)), (D[4], (3, 4))])
check('3332/support3/loopD2', counts, (D[2], D[2]), D[2],
      [(P[3], (0, 2)), (P[3], (3, 2)), (P[4], (4, 1)), (P[4], (4, 2)), (D[4], (0, 1)), (D[4], (3, 1))])

result = {'status': 'passed', 'explicit_matching_checks': len(checks), 'checks': checks,
          'scope': 'Displayed geometric witnesses only; no inventory enumeration.'}
Path(__file__).with_name('common-corner-eleven-audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'checks'}))
