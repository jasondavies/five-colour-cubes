"""Finite corroboration of alternating-path-family.md, not a proof premise."""
from itertools import product
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'root'))
from cut_model import CORNERS, CUTS, CLASSES, match_target

labels = [3, 5, 6, 8, 11, 12, 15, 16]
forbidden = {('t', 0, 4), ('t', 3, 4), ('t', 3, 1)}
assert [i for i, cut in enumerate(CUTS) if not cut & forbidden] == labels

expected = {
    (1, 0, 3, 0, 0, 3, 3, 0),
    (0, 0, 3, 0, 1, 3, 3, 0),
    (0, 3, 1, 0, 3, 0, 0, 3),
    (0, 3, 0, 1, 3, 0, 0, 3),
}
actual = set()
tested = 0
for v in product(range(4), repeat=8):
    if sum(v) != 10:
        continue
    tested += 1
    n = [0] * 75
    n[71] = n[73] = 2
    for a, amount in zip(labels, v):
        n[3 * a] = amount
    if not (match_target(n, 71) or match_target(n, 73)):
        actual.add(v)
assert actual == expected, (actual, expected)


def check_witness(target_class, entries):
    assigned = []
    for source, word in entries:
        corner = ('t', int(word[0]), int(word[1]))
        assert corner in CORNERS[source]
        assigned.append(corner)
    assert len(assigned) == 6 and set(assigned) == CUTS[target_class]


check_witness(6, [(71, '41'), (73, '01'), (73, '03'),
                  (45, '02'), (45, '42'), (36, '43')])
check_witness(12, [(36, '40'), (73, '10'), (73, '12'),
                   (71, '42'), (45, '13'), (18, '43')])

# Once the loops force all three distinct repeats in the two pole-sharing
# classes, the shared-repeat construction is independent of the third
# class's repeats. Check its direct allocation symbolically.
direct = [
    (19, ('b', 2, 0)),   # C04 repeating2
    (37, ('b', 2, 4)),   # C14 repeating2
    (71, ('t', 4, 1)),
    (73, ('t', 0, 1)),
    (73, ('t', 0, 3)),
    (45, ('t', 0, 2)),
    (45, ('t', 4, 2)),
    (36, ('t', 4, 3)),   # another C14 source
]
assert all(c in CORNERS[s] for s, c in direct)
assert len(set(c for _, c in direct)) == 8
assert set(c for _, c in direct) == CORNERS[19]

report = {
    'status': 'passed',
    'allowed_classes': labels,
    'capacity_vectors_checked': tested,
    'vectors_failing_both_P_and_Q': sorted(actual),
    'explicit_own_loops': 2,
    'explicit_cross_repeat_assembly': True,
    'proof_dependency': 'none; corroboration of written argument',
}
Path(__file__).with_name('alternating-audit.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
