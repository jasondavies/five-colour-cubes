"""Independent checks of the elementary common-corner 3322 proof.

The proof is in common-corner-3322-own-loop-hand.md. This script checks
its explicit assignments and the eighteen normalized weight placements;
neither computation is an input to the hand proof.
"""
import itertools
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "research" / "robust_route"))
from conflict_graph import CLASSES, CUTS, conflict_graph

N = {"P2": 2, "P3": 4, "P4": 6, "D2": 9, "D3": 11, "D4": 13}


def assignment(support, reserves, target, data, triples=()):
    available = {name: 3 if name in triples else 2 for name in support}
    for name in reserves:
        available[name] -= 1
    for name, arcs in data.items():
        assert len(arcs.split()) <= available[name]
    actual = []
    for name, arcs in data.items():
        for arc in arcs.split():
            c = ("t", int(arc[0]), int(arc[1]))
            assert c in CUTS[N[name]], (name, arc)
            actual.append(c)
    assert len(actual) == len(set(actual)) == 6
    assert set(actual) == CUTS[N[target]]
    p, q = CLASSES[N[reserves[0]]][0], CLASSES[N[reserves[1]]][0]
    a, b = CLASSES[N[target]][0]
    assert (a in p and b in q) or (b in p and a in q)


same = ("P4", "D2", "D3", "D4")
rows = [
    (("P4", "D2"), "P2", {"P4": "03", "D2": "01", "D3": "21 23", "D4": "04 24"}),
    (("P4", "D3"), "P3", {"P4": "02", "D2": "31 32", "D3": "01", "D4": "04 34"}),
    (("P4", "D4"), "P4", {"P4": "43", "D2": "02 42", "D3": "03 41", "D4": "01"}),
    (("D2", "D3"), "D2", {"P4": "02 42", "D2": "32", "D3": "41", "D4": "01 31"}),
    (("D2", "D4"), "D2", {"P4": "02 42", "D2": "32", "D3": "01 41", "D4": "31"}),
    (("D3", "D4"), "D3", {"P4": "03 43", "D2": "01 41", "D3": "23", "D4": "21"}),
]
for reserves, target, data in rows:
    assignment(same, reserves, target, data)

paired = ("P3", "P4", "D3", "D4")
assignment(paired, ("P3", "D4"), "P4", {
    "P3": "02", "D4": "01", "P4": "42 43", "D3": "03 41",
})

unpaired = ("P3", "P4", "D2", "D4")
assignment(unpaired, ("P3", "P3"), "P3", {
    "P4": "01 02", "D2": "31 32", "D4": "04 34",
})
assignment(unpaired, ("D2", "D2"), "D2", {
    "P3": "02 32", "P4": "41 42", "D4": "01 31",
})
assignment(unpaired, ("P3", "D4"), "P4", {
    "D4": "01", "P3": "02", "D2": "41 42", "P4": "03 43",
})
assignment(unpaired, ("P4", "D2"), "D4", {
    "P4": "01", "D2": "31", "P3": "04 34", "D4": "21 24",
})
assignment(unpaired, ("P4", "D4"), "P4", {
    "P4": "03 43", "D2": "41 42", "P3": "02", "D4": "01",
}, triples=("P4",))
assignment(unpaired, ("P4", "D4"), "D4", {
    "D4": "21 24", "P3": "04 34", "D2": "31", "P4": "01",
}, triples=("D4",))

profile_checks = 0
for support in (same, paired, unpaired):
    for triples in itertools.combinations(support, 2):
        gs = [0] * 20
        for name in support:
            gs[N[name]] = 3 if name in triples else 2
        G = conflict_graph(gs)
        for assumed in triples:
            t = N[assumed]
            loops = set(G["loops"]) | {t}
            edges = set(G["edges"])
            edges.update(tuple(sorted((t, N[name]))) for name in support
                         if N[name] != t and set(CLASSES[t][0]) & set(CLASSES[N[name]][0]))
            choices = []
            for name in support:
                j = N[name]
                palette = [r for r in range(5) if r not in CLASSES[j][0]]
                demand = gs[j] if j in loops else 1
                choices.append([set(x) for x in itertools.combinations(palette, demand)])
            for colours in itertools.product(*choices):
                use = {N[name]: colours[i] for i, name in enumerate(support)}
                assert any(use[a] & use[b] for a, b in edges), (support, triples, assumed, use)
            profile_checks += 1

report = {
    "status": "passed",
    "explicit_assignments": 13,
    "normalized_support_types": 3,
    "normalized_weight_placements": 18,
    "assumed_own_loop_checks": profile_checks,
    "proof_dependency": False,
}
out = Path(__file__).with_name("common-corner-3322-own-loop-audit.json")
out.write_text(json.dumps(report, indent=2) + "\n")
print(json.dumps(report))
