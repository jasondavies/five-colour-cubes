"""Finite catalogue, two-variety bounds and anchored Hall-cover orbits."""
import itertools
from cube_geometry import canonical, corners

def varieties(palette, used):
    return sorted({canonical(c) for c in itertools.product(range(palette), repeat=6)
                   if len(set(c)) == used})

def obstructions(cubes, target):
    """All maximal Hall-deficiency alternatives, with a representative slot mask.

    A collection x fails iff, for some nonempty set S of target slots,
    sum(x[c] for c adjacent to S) <= |S|-1. For a fixed neighbourhood keep
    the largest |S|. A smaller neighbourhood with at least that RHS subsumes
    an alternative, so the latter may also be discarded.
    """
    available = [set(corners(c)) for c in cubes]
    neighbourhoods = [sum(1 << i for i, cs in enumerate(available) if k in cs)
                      for k in corners(target)]
    masks = [0] * 256
    best = {}
    for s in range(1, 256):
        low = s & -s
        masks[s] = masks[s ^ low] | neighbourhoods[low.bit_length() - 1]
        rhs = s.bit_count() - 1
        if masks[s] not in best or best[masks[s]][0] < rhs:
            best[masks[s]] = (rhs, s)
    result = []
    for n, (rhs, s) in best.items():
        if any(m != n and m & n == m and r >= rhs
               for m, (r, _) in best.items()):
            continue
        result.append((n, rhs, s))
    return result

def geometry():
    cubes = varieties(5, 5)
    cs = [set(corners(c)) for c in cubes]
    masks = [[sum(1 << k for k, q in enumerate(corners(t)) if q in s)
              for s in cs] for t in cubes]
    opposite = [any(c[2*j] == c[2*j+1] for j in range(3)) for c in cubes]
    anchors = [opposite.index(False), opposite.index(True)]
    for anchor, flag in zip(anchors, (False, True)):
        orbit = {canonical(tuple(p[a] for a in cubes[anchor]))
                 for p in itertools.permutations(range(5))}
        assert orbit == {c for c, f in zip(cubes, opposite) if f == flag}
    pairs = {}
    for i in range(75):
        for j in range(i+1, 75):
            winning = set()
            for row in masks:
                if row[i] | row[j] == 255:
                    winning.update(range(max(1, 8-row[j].bit_count()),
                                         min(7, row[i].bit_count())+1))
            if winning:
                pairs[i, j] = sorted(winning)
    return cubes, opposite, anchors, pairs, [obstructions(cubes, t) for t in cubes]

def covers(data, kind, m):
    cubes, _, anchors, _, _ = data
    anchor=anchors[kind]
    tc=corners(cubes[anchor])
    fit=[sum(1<<k for k,q in enumerate(tc) if q in set(corners(c))) for c in cubes]
    index={c:i for i,c in enumerate(cubes)}
    group=[]
    for p in itertools.permutations(range(5)):
        for mirror in (False,True):
            def image(c):
                c=tuple(p[a] for a in c)
                if mirror:c=(c[1],c[0],*c[2:])
                return index[canonical(c)]
            if image(cubes[anchor])==anchor:
                group.append([image(c) for c in cubes])
    reps={}
    for k in range(256):
        if k.bit_count()>7-m:continue
        bad=sum(1<<i for i,mask in enumerate(fit) if i!=anchor and mask & ~k)
        budget=7-m-k.bit_count()
        key=min(sum(1<<p[i] for i in range(75) if bad>>i&1) for p in group),budget
        reps.setdefault(key,(bad,budget,k))
    return sorted(reps.values(),key=lambda x:(x[1],x[0]))
