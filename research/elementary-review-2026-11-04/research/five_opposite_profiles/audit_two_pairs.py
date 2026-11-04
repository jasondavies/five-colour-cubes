"""Independent finite corroboration of the written two-pairs hand proof.

The proof does not use the inventory check. Run from repository workspace:
  python3 research/five_opposite_profiles/audit_two_pairs.py
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'root'))
from cut_model import CORNERS, CUTS, solution


def cut(s):
    return {('t', a, b) for a in s for b in range(5) if b not in s}


def corners(words):
    return {('t', int(w[0]), int(w[1])) for w in words.split()}


def edges(o):
    return {tuple(sorted(c[1:])) for c in CORNERS[o]}


A = cut({0, 1})
# Entries: P,Q,R,target,B-outset, assignments for P,P,Q,Q,R,A,A,B.
# For the first matching, R only needs the bidirected edge14.
witnesses = [
    (65, 73, None, 61, {0, 1, 2}, '34 43 21 32 41 12 14 23'),
    (65, 70, 64, 65, {0, 1, 4}, '34 30 42 24 20 02 03 43'),
    (61, 65, 71, 65, {0, 1, 4}, '43 34 30 24 20 02 03 42'),
    (61, 65, 73, 61, {0, 1, 3}, '41 23 43 34 21 12 14 32'),
]
for p, q, r, t, b, words in witnesses:
    rp = CORNERS[r] if r is not None else corners('14 41')
    source_sets = [CORNERS[p]] * 2 + [CORNERS[q]] * 2 + [rp, A, A, cut(b)]
    assigned = list(words.split())
    assert len(assigned) == 8 and corners(words) == CORNERS[t]
    assert all(next(iter(corners(c))) in source for c, source in zip(assigned, source_sets))

rescue_claims = [
    ('23 32 24 42 30', [A]),
    ('01 10 30 34 43', [A, cut({0, 1, 2})]),
    ('20 34 43 23 32', [A]),
    ('01 10 21 23 32', [A, cut({0, 1, 4})]),
    ('21 23 32 01 10', [A, cut({0, 1, 4})]),
    ('20 24 42 01 10', [A, cut({0, 1, 3})]),
    ('20 24 42 34 43', [A]),
    ('21 23 32 34 43', [A]),
]
for words, expected in rescue_claims:
    actual = [c for c in CUTS if not c & corners(words)]
    assert {frozenset(c) for c in actual} == {frozenset(c) for c in expected}

counts = Counter()
for p, q in combinations(range(60, 75), 2):
    profile = 'neighbouring' if len(edges(p) & edges(q)) == 2 else 'nonneighbouring'
    for r in range(60, 75):
        if r in (p, q):
            continue
        for b in range(1, 20):
            n = [0] * 75
            n[p] = n[q] = 2
            n[r] = 1
            n[0] = 2
            n[3 * b] += 1
            assert solution(n, range(60, 75)) is not None, (p, q, r, b)
            counts[profile] += 1

report = {
    'status': 'passed',
    'explicit_exception_witnesses': len(witnesses),
    'rescue_set_claims': len(rescue_claims),
    'inventories_at_fixed_adjacent_class': dict(counts),
    'total_inventories': sum(counts.values()),
    'proof_dependency': 'none; finite corroboration of written elementary argument',
}
out = Path(__file__).with_name('two-pairs-audit.json')
out.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
