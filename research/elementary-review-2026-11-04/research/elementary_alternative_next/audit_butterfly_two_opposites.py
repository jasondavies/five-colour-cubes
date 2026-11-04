"""Audit the geometric identities in the butterfly two-opposite proof.

No source-inventory enumeration is performed.  The finite checks concern
the fixed symmetries, allowed opposite shapes, and displayed assignments.
"""
from collections import Counter
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "root"))
from cut_model import CLASSES, CUTS, CORNERS, ADJ

IDS = {"A": 0, "P": 2, "L": 5, "M": 7, "U": 8, "V": 19}
C = {name: CUTS[j] for name, j in IDS.items()}
OIDS = {"X": 63, "Y": 64, "Z": 65, "R": 70, "S": 73}
C.update({name: CORNERS[j] for name, j in OIDS.items()})

def arc(text):
    return ("t", int(text[0]), int(text[1]))

def transformed(corners, perm, reverse=False):
    return frozenset(("t", perm[y], perm[x]) if reverse
                     else ("t", perm[x], perm[y])
                     for _, x, y in corners)

counts = Counter()

for perm, reverse in [((0, 2, 1, 3, 4), False),
                      ((0, 1, 2, 4, 3), False),
                      ((0, 3, 4, 1, 2), True)]:
    assert {transformed(C[name], perm, reverse) for name in IDS} == {
        C[name] for name in IDS}
    counts["butterfly_symmetries"] += 1
assert {transformed(C[name], (0, 3, 4, 1, 2), True)
        for name in ("A", "P")} == {C["L"], C["M"]}
assert transformed(C["U"], (0, 3, 4, 1, 2), True) == C["V"]

for corner, names in [("13", "ALUV"), ("14", "AMUV"),
                      ("23", "PLUV"), ("24", "PMUV")]:
    assert all(arc(corner) in C[name] for name in names)
    counts["common_corner_families"] += 1

missing = {arc(s) for s in ("31", "32", "41", "42")}
all_arcs = {("t", a, b) for a in range(5) for b in range(5) if a != b}
assert all_arcs - set.union(*(set(C[name]) for name in IDS)) == missing
assert all(CORNERS[j] & missing for j in range(60, 75))
avoiders = {j for j in range(60, 75)
            if not (CORNERS[j] & {arc("31"), arc("41")})}
assert avoiders == set(OIDS.values())
counts["exact_avoiding_opposite_lists"] = 1
for name, expected in [("X", ("32", "42")), ("Y", ("32",)),
                       ("Z", ("42",)), ("R", ("42",)),
                       ("S", ("32",))]:
    assert C[name] & missing == {arc(s) for s in expected}

def check(target, assignments, capacities, special=None):
    sources = dict(C)
    if special:
        sources.update(special)
    assigned = [arc(c) for name, corners in assignments.items() for c in corners]
    assert len(assigned) == len(set(assigned)) == len(target)
    assert set(assigned) == set(target)
    for name, corners in assignments.items():
        assert len(corners) <= capacities[name], (name, corners, capacities)
        assert all(arc(c) in sources[name] for c in corners), (name, corners)
    counts["displayed_assignments"] += 1

# (2), both low choices, every geometrically eligible opposite.
for oi in range(60, 75):
    if arc("31") not in CORNERS[oi]:
        continue
    for low in ("U", "V"):
        check(CORNERS[67],
              {"O": ["31"], "P": ["01"], "L": ["40", "43"],
               "M": ["10", "34"], "A": ["04"], low: ["13"]},
              {"O": 1, "P": 1, "L": 2, "M": 2, "A": 1, low: 1},
              {"O": CORNERS[oi]})
    # (4).
    check(CORNERS[67],
          {"O": ["31"], "P": ["01"], "L": ["40", "43"],
           "M": ["10", "34"], "V": ["04"], "U": ["13"]},
          {"O": 1, "P": 1, "L": 2, "M": 2, "V": 1, "U": 1},
          {"O": CORNERS[oi]})

# Mixed missing-corner template: the four forward positions are available
# independently from each P or V copy, so only their sum matters.
assert {arc(s) for s in ("03", "04", "23", "24")} <= C["P"] & C["V"]
assert arc("30") in C["M"] and arc("40") in C["L"]
assert {arc(s) for s in ("03", "04", "23", "24", "30", "40", "32", "42")} == CORNERS[63]
counts["flexible_four_forward_template"] = 1

# (5): another Y or S source supplies32.
for other in ("Y", "S"):
    check(CORNERS[64],
          {"Y1": ["02"], "O2": ["32"], "P": ["04"],
           "M": ["34"], "L": ["40", "43", "20"], "U": ["23"]},
          {"Y1": 1, "O2": 1, "P": 1, "M": 1, "L": 3, "U": 1},
          {"Y1": C["Y"], "O2": C[other]})

# (6).
check(CORNERS[73],
      {"S": ["12", "32"], "P": ["01", "21"],
       "M": ["10", "30"], "V": ["03"], "U": ["23"]},
      {"S": 2, "P": 2, "M": 2, "V": 1, "U": 1})

# (8), (9): capacities record the two reservations in the own class.
loop_m = {"M": ["34"], "S": ["30"], "P": ["24"],
          "L": ["10", "20"], "U": ["14"]}
check(C["M"], loop_m, {"M": 1, "S": 2, "P": 1, "L": 3, "U": 3})
check(C["V"],
      {"V": ["04"], "S": ["03"], "P": ["24"],
       "L": ["13", "23"], "M": ["14"]},
      {"V": 1, "S": 2, "P": 1, "L": 3, "M": 3})

# Final cross-class bicoloured reservation, with one of the two remaining
# M sources at34 and no V source used in loop_m.
mi = ADJ.index((IDS["M"], 1))
vi = ADJ.index((IDS["V"], 1))
assert ("b", 1, 0) in CORNERS[mi]
assert ("b", 1, 4) in CORNERS[vi]
assert set(CORNERS[mi]) == set(C["M"]) | {("b", 1, 0), ("b", 1, 4)}
assert "V" not in loop_m and len(loop_m["M"]) <= 2
counts["final_cross_class_completion"] = 1

result = {"status": "passed", "checks": dict(counts),
          "inventory_enumeration": False}
out = Path(__file__).with_name("butterfly-two-opposites-audit.json")
out.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
