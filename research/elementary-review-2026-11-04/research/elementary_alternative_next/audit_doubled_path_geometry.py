"""Independent fixed-geometry audit of the two doubled-core path proofs.

The hand audit of Hall and count arguments is recorded separately.
This script checks fixed cut lists, small position-set tables, symmetries,
and explicit assignments. It does not enumerate source inventories.
"""
from collections import Counter
from itertools import combinations, permutations, product
from pathlib import Path
import json
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "root"))
from cut_model import V, CUTS, CORNERS

def arc(s):
    return ("t", int(s[0]), int(s[1]))

def arcs(ss):
    return frozenset(arc(s) for s in ss.split())

def cut(label):
    outset = {int(c) for c in label}
    return frozenset(("t", a, b) for a in outset for b in V if b not in outset)

def transform(corners, p, rev=False):
    return frozenset(("t", p[b], p[a]) if rev else ("t", p[a], p[b])
                     for _, a, b in corners)

checks = Counter()
D = CORNERS[60]
forms = [
    ("monotone", "24 32 41", ["01", "124", "14", "014"], [67, 72]),
    ("one-change", "24 31 41", ["01", "134", "124", "13", "14", "014", "013"], [64, 73]),
    ("alternating", "32 41 42", ["01", "02", "124", "123", "12", "023", "23", "012"], [67, 72]),
]
for name, missing, allowed, singles in forms:
    absent = arcs(missing)
    assert {c for c in CUTS if not c & absent} == {cut(s) for s in allowed}, name
    assert {i for i in range(60, 75) if len(CORNERS[i] & D) == 2
            and not CORNERS[i] & absent} == set(singles), name
    checks["exact_forbidden_cut_and_marked_single_lists"] += 1
assert all(arc("13") in cut(s) for s in forms[0][2])

# Full geometry classification: four choices of the remaining common edge,
# and both directions on each of the other three edges. Preserve the marked
# doubled target; do not assume that an individual single P is fixed.
edges = [(1, 3), (1, 4), (2, 3), (2, 4)]
all_path_absences = set()
for excluded in range(4):
    path = [edge for i, edge in enumerate(edges) if i != excluded]
    for dirs in product([False, True], repeat=3):
        all_path_absences.add(frozenset(("t", b, a) if rev else ("t", a, b)
                                      for (a, b), rev in zip(path, dirs)))
covered = set()
for p in permutations(V):
    if transform(D, p) != D:
        continue
    for rev in [False, True]:
        for _, missing, _, _ in forms:
            covered.add(transform(arcs(missing), p, rev))
assert covered == all_path_absences and len(covered) == 32
checks["three_geometric_path_forms"] = 1
p = (0, 3, 4, 1, 2)
assert transform(D, p, True) == D
assert transform(arcs("32 41 42"), p, True) == arcs("32 41 42")
assert transform(CORNERS[67], p, True) == CORNERS[72]
checks["alternating_marked_single_exchange"] = 1

one = dict(zip("ABCEFGH", [cut(s) for s in forms[1][2]]))
one.update(D=D, P=CORNERS[64])
R = arcs("02 04 20 34 40 43")
expected = dict(A="02 04", B="40", C="20 40 43", E="34",
                F="40 43", G="02 43", H="02 04 34")
for name, positions in expected.items():
    assert one[name] & R == arcs(positions)
for size in [1, 2, 3]:
    for positions in combinations(R, size):
        assert sum((one[name] & R) <= set(positions) for name in expected) <= size
checks["one_change_Konig_containment_bounds"] = 1
actual = {frozenset(missing): frozenset(name for name in expected
                                      if not one[name] & set(missing))
          for missing in combinations(R, 2)}
actual = {missing: names for missing, names in actual.items() if len(names) >= 4}
listed = {arcs(pos): frozenset(names) for pos, names in [
    ("04 20", "BEFG"), ("20 34", "ABFG"), ("20 40", "AEGH"),
    ("20 43", "ABEH"), ("02 04", "BCEF"), ("04 34", "BCFG")
]}
assert actual == listed
checks["one_change_missing_pair_table"] = 1

def check(target, assignments, sources, capacities=None):
    chosen = []
    for name, text in assignments.items():
        points = arcs(text)
        assert points <= sources[name], (name, text)
        if capacities:
            assert len(points) <= capacities[name], (name, text, capacities)
        chosen.extend(points)
    assert len(chosen) == 8 and len(set(chosen)) == 8
    assert set(chosen) == set(CORNERS[target])
    checks["explicit_eight_source_assignments"] += 1

for row in [
    dict(G="03", P="04", D="23 24", B="40 42", E="30 32"),
    dict(A="03 04", P="23", D="24 42", B="30 32", F="40"),
    dict(A="03 04", P="40", D="23 24", E="30 32", G="42"),
    dict(A="03 04", P="23", D="24 42", B="32 40", E="30"),
    dict(G="03", P="04", D="24 42", B="30 32", C="23 40"),
]:
    check(63, row, one, {name: 1 if name == "P" else 2 for name in one})

# Pattern table for one-change P=O73 after its21 and D's41 reservations.
remaining = arcs("12 14 23 32 34 43")
for name, positions in dict(A="12 14", B="12 32", C="23 43",
                            E="12 14 32 34", H="12 14 32 34",
                            F="12 43", G="12 43").items():
    assert one[name] & remaining == arcs(positions)
checks["one_change_six_position_pattern_table"] = 1
assert arcs("02 03") <= one["A"] & one["G"]
assert all(arc("12") in one[name] for name in "ABFG")
assert arc("20") in one["C"] and arc("30") in one["B"]

alt = dict(zip("ABCEFGHJ", [cut(s) for s in forms[2][2]]))
alt.update(D=D, P=CORNERS[67])
for target, row in [
    (71, dict(D="41 42", P="01", A="02 14", E="10 20", G="24")),
    (67, dict(D="13 31", P="43", C="40", G="34", F="10", B="01", J="04")),
    (67, dict(D="13 31", P="43", C="40", G="01 04", F="10", H="34")),
    (61, dict(D="32 41", P="34", A="12 14", B="21", C="43", J="23")),
]:
    check(target, row, alt, {name: 1 if name == "P" else 2 for name in alt})

K = arcs("01 04 10 34")
expected = dict(A="04", J="04", B="01 04", E="10 34",
                F="10", G="01 04 34", H="34")
for name, positions in expected.items():
    assert alt[name] & K == arcs(positions)
actual = {frozenset(pair): frozenset(name for name in expected
                                   if alt[name] & K <= set(pair))
          for pair in combinations(K, 2)}
actual = {pair: names for pair, names in actual.items() if len(names) >= 3}
listed = {arcs(pos): frozenset(names) for pos, names in [
    ("01 04", "ABJ"), ("04 10", "AFJ"),
    ("04 34", "AHJ"), ("10 34", "EFH")
]}
assert actual == listed
checks["alternating_Konig_pattern_and_pair_tables"] = 1
assert not alt["A"] & alt["H"]
assert all(arc("13") in alt[name] for name in "ACFJ")
assert all(arc("20") in alt[name] for name in "CEFH")

result = {"status": "passed", "checks": dict(checks),
          "inventory_enumeration": False}
out = Path(__file__).with_name("doubled-path-geometric-audit.json")
out.write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
