"""Exact 20-cut / 15-biclique corner model for exploratory mathematics.

This is an independent model, not a proof of completeness of any search.
Tri-coloured corners are directed complementary pairs ('t', a, b).
Bi-coloured corners are ('b', repeated_colour, singleton_colour).
"""
from itertools import combinations, permutations
from collections import Counter

V = tuple(range(5))
PAIRS = tuple(combinations(V, 2))
CLASSES = tuple((p, s) for p in PAIRS for s in (1, -1))

def cut(p, s):
    return frozenset(('t', a, b) if s == 1 else ('t', b, a)
                     for a in p for b in V if b not in p)

CUTS = tuple(cut(p, s) for p, s in CLASSES)
ADJ = tuple((j, r) for j, (p, s) in enumerate(CLASSES) for r in V if r not in p)
OPP = []
for r in V:
    left = [v for v in V if v != r]
    for b in left[1:]:
        p = (left[0], b)
        q = tuple(v for v in left if v not in p)
        OPP.append((r, p, q))
OPP = tuple(OPP)
KINDS = tuple(('a', j, r) for j, r in ADJ) + tuple(('o', *o) for o in OPP)
CORNERS = tuple(CUTS[j] | frozenset(('b', r, p) for p in CLASSES[j][0])
                for j, r in ADJ) + tuple(
                    frozenset(('t', a, b) for p, q in ((p,q),(q,p)) for a in p for b in q)
                    for r, p, q in OPP)
assert len(CORNERS) == len(set(CORNERS)) == 75
assert all(len(c) == 8 for c in CORNERS)
TARGETS = tuple(tuple(sorted(c)) for c in CORNERS)
MASKS = tuple(tuple(sum(1 << k for k, c in enumerate(t) if c in source)
                    for source in CORNERS) for t in TARGETS)

def match_target(counts, target):
    copies = [s for s, n in enumerate(counts) for _ in range(n)]
    masks = [MASKS[target][s] for s in copies]
    order = sorted(range(8), key=lambda k: sum(bool(m & (1 << k)) for m in masks))
    owners = [-1] * len(copies)
    def augment(k, seen):
        for i, m in enumerate(masks):
            if i in seen or not (m & (1 << k)):
                continue
            seen.add(i)
            if owners[i] < 0 or augment(owners[i], seen):
                owners[i] = k
                return True
        return False
    return all(augment(k, set()) for k in order)

def solution(counts, targets=range(75)):
    return next((t for t in targets if match_target(counts, t)), None)

def coarse(counts):
    gs = [sum(counts[3*j:3*j+3]) for j in range(20)]
    os = counts[60:]
    return gs, os

def W(counts):
    gs, os = coarse(counts)
    o = sum(os)
    return 3*sum(g*(g-1)//2 for g in gs)-4*o*(o-1)//2

if __name__ == '__main__':
    t = CORNERS[60]
    groups = {}
    for j,c in enumerate(CUTS):
        groups.setdefault(tuple(sorted(c & t)), []).append(j)
    print('Opposite normal form:', OPP[0])
    for key,js in sorted(groups.items()):
        print(key, [(j,CLASSES[j]) for j in js])
