"""Small exact checks accompanying the elementary research notes.

Run from any directory: python3 path/to/verify_research.py
Python standard library only. These are audits of the notes, not a proof
of the still-open global fourteen-failure classification.
"""
from pathlib import Path
import itertools
import random
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / 'robust_route'))
from cut_model import *
from conflict_graph import conflict_graph, refinement_respects_graph


def compositions(n, k, cap=None):
    if k == 1:
        if cap is None or n <= cap:
            yield (n,)
        return
    for a in range(min(n, cap) + 1 if cap is not None else n + 1):
        for rest in compositions(n-a, k-1, cap):
            yield (a,) + rest


def partitions(n, minimum=1):
    if n == 0:
        yield ()
    for a in range(minimum, n+1):
        for rest in partitions(n-a, a):
            yield (a,) + rest


def check_window():
    tested = 0
    for o in range(16):
        for gs in partitions(15-o):
            a = sum(g*(g-1)//2 for g in gs)
            w = 3*a - 4*o*(o-1)//2
            ds = [w-3*(g-1) for g in gs]
            if o:
                ds.append(w+4*(o-1))
            assert not all(31 <= x <= 38 for x in ds)
            tested += 1
    print(f'Deletion-window audit: {tested} numerical fifteen-profiles; no exception.')


def check_opposite_geometry():
    assert len(set(CORNERS)) == 75
    assert all(len(c) == 8 for c in CORNERS)
    assert all(len(c & t) in (2, 4, 8)
               for c in CORNERS for t in CORNERS[60:])
    target = CORNERS[60]
    actions = []
    for p in itertools.permutations(V):
        for rev in (False, True):
            def tr(c, p=p, rev=rev):
                return frozenset(('t',p[b],p[a]) if rev else ('t',p[a],p[b])
                                 for _,a,b in c)
            if tr(target) == target:
                actions.append(tr)
    assert len(actions) == 16
    for size, expected in [(3, 5), (4, 10)]:
        left = set(map(frozenset, itertools.combinations(target, size)))
        sizes = []
        while left:
            c = min(left, key=lambda c: sorted(c))
            orbit = {f(c) for f in actions}
            left -= orbit
            sizes.append(len(orbit))
        assert len(sizes) == expected
        print(f'Opposite-target {size}-corner covers: {expected} symmetry types; '
              f'{sum(sizes)} subsets accounted for.')
    for y in range(75):
        x = [0]*75
        x[60], x[67], x[72] = 3, 2, 2
        x[y] += 1
        assert solution(x, range(60,75)) is not None
    print('Three-plus-two-plus-two opposite core: all 75 eighth sources checked.')


def check_refinements():
    failures = 0
    for a in compositions(5, 3):
        for b in compositions(5, 3):
            x = [0]*75
            x[60] = 4
            x[:3] = a
            x[15:18] = b
            predicted = a[0]*b[1] == 0 and a[2]*b[2] == 0
            actual = solution(x) is None
            assert actual == predicted
            failures += actual
    assert failures == 91
    print('Opposite-four normal form: all 441 refinements checked; exactly 91 fail.')

    failures = 0
    for a in compositions(5, 3):
        for b in compositions(3, 3):
            for c in compositions(3, 3):
                x = [0]*75
                x[60] = 3
                x[:3], x[15:18], x[24:27] = a, b, c
                actual = solution(x) is None
                predicted = a == (5,0,0) and b == (3,0,0) and c == (1,1,1)
                assert actual == predicted
                failures += actual
    assert failures == 1
    print('Opposite-three normal form: all 2,100 refinements checked; exactly one fails.')

    failures = 0
    high = {1:0, 2:2, 3:5, 4:7}
    for perm in itertools.permutations((1,2,3,4)):
        if any(i == r for i,r in zip((1,2,3,4),perm)):
            continue
        x = [0]*75
        x[ADJ.index((8,0))] = x[ADJ.index((19,0))] = 1
        for v,r in zip((1,2,3,4),perm):
            x[ADJ.index((high[v],r))] = 3
        assert solution(x) is None
        assert W(x) == 36
        failures += 1
    assert failures == 9
    print('Pure butterfly: all nine derangement refinements fail, each with W=36.')


def robust(gs, t):
    cs = tuple(CUTS[t])
    for mask in range(1,64):
        d = {cs[k] for k in range(6) if mask >> k & 1}
        if sum(g for j,g in enumerate(gs) if CUTS[j] & d) < len(d)+2:
            return False
    return True


def check_hall_formulas():
    common = [2,4,6,9,11,13]
    butterfly = [0,2,5,7,8,19]
    tested = 0
    for vv in compositions(14,6,5):
        a,b = vv[:3],vv[3:]
        gs = [0]*20
        for j,v in zip(common,vv):
            gs[j] = v
        for i in range(3):
            j,k = [z for z in range(3) if z != i]
            stated = (a[i]+b[j]>=3 and a[i]+b[k]>=3 and
                      a[i]+b[j]+b[k]>=5 and
                      a[i]+a[j]+b[k]>=4 and a[i]+a[k]+b[j]>=4 and
                      a[i]+a[j]+b[j]+b[k]>=6 and
                      a[i]+a[k]+b[j]+b[k]>=6 and 14-b[i]>=7)
            assert stated == robust(gs,common[i])
        gs = [0]*20
        for j,v in zip(butterfly,vv):
            gs[j] = v
        x1,x2,x3,x4,u,v = vv
        l,r = x1+x2+v,x3+x4+u
        assert robust(gs,8) == (r >= 4)
        assert robust(gs,19) == (l >= 4)
        assert robust(gs,0) == (x1>=4 and l>=6 and
                                14-x2-x3>=5 and 14-x2-x4>=5)
        tested += 1
    assert tested == 4221
    print(f'Pure-family Hall formulas: {tested} count profiles checked in each family.')


def check_graph_reduction():
    rng = random.Random(20261103)
    for _ in range(120):
        chosen = rng.sample(range(20), rng.randrange(2,8))
        gs,os = [0]*20,[0]*15
        for _ in range(rng.randrange(0,5)):
            os[rng.randrange(15)] += 1
        for _ in range(14-sum(os)):
            gs[rng.choice(chosen)] += 1
        graph = conflict_graph(gs,os)
        for _ in range(3):
            x = [0]*60+os
            for j,g in enumerate(gs):
                for _ in range(g):
                    x[3*j+rng.randrange(3)] += 1
            assert refinement_respects_graph(x,graph) == (solution(x,range(60)) is None)
    print('Conflict graph: 360 seeded refinements agree with independent eight-corner matching.')


if __name__ == '__main__':
    check_window()
    check_opposite_geometry()
    check_refinements()
    check_hall_formulas()
    check_graph_reduction()
    print('All checks passed. The global exhaustion lemma is still unproved.')

