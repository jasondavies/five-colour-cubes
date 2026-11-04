"""Corroboration of neighbouring-pairs-four-classes.md, not a proof premise."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'root'))
from cut_model import CORNERS, CUTS, solution

reports = []
for p, q, t, kind in [(60, 61, 62, 'K4'), (60, 63, 66, 'K2,3')]:
    i = CORNERS[p] & CORNERS[q]
    j = CORNERS[p] - i
    k = CORNERS[q] - i
    assert j | k == CORNERS[t]
    small = [c for c in CUTS if [len(c & block) for block in [i, j, k]] == [1, 1, 1]]
    max_corner_frequency = max(sum(corner in c for c in small) for corner in i | j | k)
    assert max_corner_frequency <= 3
    for target in [p, q, t]:
        patterns = Counter(c & CORNERS[target] for c in CUTS if len(c & CORNERS[target]) == 2)
        assert max(patterns.values()) <= 2
    tested = 0
    for aa in combinations(range(20), 4):
        n = [0] * 75
        n[p] = n[q] = 2
        for a in aa:
            n[3 * a] = 1
        assert solution(n, [p, q, t]) is not None, (kind, aa)
        tested += 1
    reports.append({'line': kind, 'distinct_class_selections': tested,
                    '111_classes': len(small), 'max_111_corner_frequency': max_corner_frequency})

out = {'status': 'passed', 'line_types': reports,
       'total_selections': sum(r['distinct_class_selections'] for r in reports),
       'proof_dependency': 'none; corroboration only'}
Path(__file__).with_name('neighbouring-audit.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
