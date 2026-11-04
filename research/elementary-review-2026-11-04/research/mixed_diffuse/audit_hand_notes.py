"""Independent exact-matching audit of the new hand-proof cores.

The prose proofs do not rely on this finite check. It checks their
local matching assertions in the independently maintained corner model.
"""
import itertools
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.extend([str(HERE.parent / 'root'), str(HERE.parent / 'robust_route'), str(HERE)])
from cut_model import solution
from conflict_graph import conflict_graph
from check_four_adj_four_opp import cases

ZERO = (1, 14, 16, 18)

def core(a, zs, ops):
    x = [0] * 75
    x[0] = a
    for j in zs:
        x[3 * j] += 1
    for o in ops:
        x[o] += 1
    assert solution(x, range(60, 75)) is not None, (a, zs, ops)

counts = {}
for label, a, z, o, restriction in [
    ('4A+3Z+O', 4, 3, 1, 'any'),
    ('3A+3Z+2O', 3, 3, 2, 'any'),
    ('3A+4Z+O', 3, 4, 1, 'any'),
    ('4A+2Z+2distinctO', 4, 2, 2, 'distinct'),
    ('3A+2Z+3diffuseO', 3, 2, 3, 'diffuse'),
]:
    tested = 0
    for ops in itertools.combinations_with_replacement(range(60, 75), o):
        if restriction == 'distinct' and len(set(ops)) != o:
            continue
        if restriction == 'diffuse' and max(ops.count(p) for p in set(ops)) > 2:
            continue
        for zs in itertools.combinations_with_replacement(ZERO, z):
            core(a, zs, ops)
            tested += 1
    counts[label] = tested

tested = 0
for row in cases():
    for j, k in itertools.combinations_with_replacement(row['classes'], 2):
        x = [0] * 75
        x[0] = 4
        x[60:] = row['os']
        x[3 * j] += 1
        x[3 * k] += 1
        assert solution(x, range(60, 75)) is not None
        tested += 1
counts['four-opposite three-corner cores with two helpers'] = tested

for profile in set(itertools.permutations((3, 3, 2))):
    gs = [0] * 20
    gs[0] = 4
    for j, n in zip((4, 6, 9), profile):
        gs[j] = n
    os = [0] * 15
    os[5] = 2
    graph = conflict_graph(gs, os)
    assert {4, 6, 9} <= set(graph['loops'])
    assert {(4, 6), (4, 9), (6, 9)} <= set(graph['edges'])
counts['homogeneous-O2 repeated-colour triangles'] = 3

result = {'status': 'all local hand-proof assertions checked', 'checks': counts}
(HERE / 'hand-notes-audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
