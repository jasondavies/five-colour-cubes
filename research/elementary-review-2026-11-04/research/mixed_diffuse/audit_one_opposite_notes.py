"""Independent audit of the one-opposite hand proof.

This checks its structural reductions and matching/colour certificates.
The written proof does not rely on the finite enumeration here.
"""
import itertools
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.extend([str(HERE), str(HERE.parent / 'root'), str(HERE.parent / 'robust_route')])
from cut_model import CUTS, solution, match_target
from conflict_graph import conflict_graph, clique_obstruction
from check_double_covers import allocations
from check_g4_three_cover import cases

summary = []
for h, js, os in cases(1):
    zeros = [i for i, j in enumerate(js) if not CUTS[j] & CUTS[0]]
    checked = opposite_failures = loop_eliminations = clique_eliminations = 0
    for gg in allocations(9, [4] * len(js)):
        if sum(gg[i] for i in zeros) > 2:
            continue
        gs = [0] * 20
        gs[0] = 4
        for j, n in zip(js, gg):
            gs[j] = n
        if any(gs[j] + gs[k] > 7 for j in range(20) for k in range(j)
               if len(CUTS[j] & CUTS[k]) == 4):
            continue
        checked += 1
        x = [v for g in gs for v in (g, 0, 0)] + list(os)
        if solution(x, range(60, 75)) is not None:
            continue
        opposite_failures += 1
        graph = conflict_graph(gs, os)
        if any(gs[j] == 4 for j in graph['loops']):
            loop_eliminations += 1
            continue
        assert clique_obstruction(gs, graph), (h, gs, os, graph)
        clique_eliminations += 1
    summary.append({
        'H': sorted(h),
        'opposite_sources': [(60 + i, n) for i, n in enumerate(os) if n],
        'coarse_vectors': checked,
        'opposite_failures': opposite_failures,
        'loop_eliminations': loop_eliminations,
        'clique_eliminations': clique_eliminations,
    })

# Check the new path reduction without invoking the conflict graph.
path_classes = (2, 4, 6, 9, 11, 13)
families = ({4, 6, 9}, {2, 6, 11}, {2, 4, 13})
path_checks = path_reductions = 0
for ns in allocations(9, [4] * 6):
    gs = [0] * 20
    gs[0] = 4
    for j, n in zip(path_classes, ns):
        gs[j] = n
    if any(gs[j] + gs[k] > 7 for j in path_classes for k in path_classes
           if j < k and len(CUTS[j] & CUTS[k]) == 4):
        continue
    path_checks += 1
    x = [v for g in gs for v in (g, 0, 0)] + [0] * 15
    x[65] = 1
    if match_target(x, 62):
        continue
    support = {j for j in path_classes if gs[j]}
    if any(support <= f for f in families):
        path_reductions += 1
        continue
    assert support <= {6, 9, 11}
    assert match_target(x, 60)

# All three newly used repeated-colour triangles.
for classes, o in [((4, 6, 9), 65), ((2, 4, 13), 65), ((6, 9, 11), 73)]:
    gs = [0] * 20
    gs[0] = 4
    for j in classes:
        gs[j] = 3
    os = [0] * 15
    os[o - 60] = 1
    graph = conflict_graph(gs, os)
    assert set(classes) <= set(graph['loops'])
    assert set(itertools.combinations(classes, 2)) <= set(graph['edges'])

result = {
    'status': 'all checks passed',
    'three_corner_covers': summary,
    'path_vectors': path_checks,
    'path_support_family_reductions': path_reductions,
    'repeated_colour_triangles': 3,
    'missing_pair_bounds_used': False,
}
(HERE / 'one-opposite-hand-proof-audit.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result, indent=2))
