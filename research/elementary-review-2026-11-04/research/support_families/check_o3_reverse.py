"""Check the small Hall formulas used in o3-reverse-family.md.

The document contains the proof; this script is an independent arithmetic
and model audit, not a substitute for its argument.
"""
from itertools import product
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "root"))
import cut_model as m

classes = [0, 10, 12, 3, 15, 17]
hall = {}
for q, j in enumerate(classes):
    target = tuple(m.CUTS[j])
    requirements = []
    for subset in range(1, 64):
        needed = [target[k] for k in range(6) if subset >> k & 1]
        neighbours = [p for p, i in enumerate(classes)
                      if any(c in m.CUTS[i] for c in needed)]
        opposite_contribution = 3 * any(c in m.CORNERS[60] for c in needed)
        requirements.append((neighbours, len(needed) + 2 - opposite_contribution))
    hall[q] = requirements

checked = 0
for g in product(range(6), repeat=6):
    if sum(g) != 11:
        continue
    a, b, c, d, e, f = g
    formula = {
        1: b+d >= 3 and b+f >= 3 and b+c+d >= 4 and b+d+f >= 4 and b+c+d+f >= 5,
        2: c+d >= 3 and c+e >= 3 and b+c+d >= 4 and c+d+e >= 4 and b+c+d+e >= 5,
        3: b+d >= 3 and c+d >= 3 and b+c+d >= 5,
        5: a+f >= 3 and b+f >= 3 and a+b+f >= 4 and a+e+f >= 4 and a+b+e+f >= 5,
    }
    for q, value in formula.items():
        direct = all(sum(g[p] for p in ns) >= minimum for ns, minimum in hall[q])
        assert value == direct, (g, q, value, direct)
    if a+e >= 1 and a+f >= 1 and a+e+f >= 2 and b+d >= 1 and c+d >= 1 and b+c+d >= 2:
        counts = [0] * 75
        counts[60] = 3
        for j, n in zip(classes, g):
            counts[3*j] = n
        assert m.match_target(counts, 63), g
    checked += 1

print(f"Checked {checked} count profiles: all four Hall formulas and the opposite construction agree.")
