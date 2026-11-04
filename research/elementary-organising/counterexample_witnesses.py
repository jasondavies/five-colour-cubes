"""Print explicit matchings and Hall witnesses for the sharp 12-source example."""
from replacement_geometry import CORNERS, CUTS
from itertools import combinations
pool=[0,1,2,45,46,47,18,18,18,36,36,63]
print('Sources by physical slot:', list(enumerate(pool)))
for j in (0,15):
    slots=list(range(12))
    for _ in range(2):
        slots.remove(next(i for i in slots if pool[i]<60 and pool[i]//3==j))
    req=sorted(CUTS[j]); owner={}
    def aug(k,seen):
        for i in slots:
            if i in seen or req[k] not in CORNERS[pool[i]]: continue
            seen.add(i)
            if i not in owner or aug(owner[i],seen):
                owner[i]=k
                return True
        return False
    assert all(aug(k,set()) for k in range(6))
    print('Own completion class',j,[(req[k],i,pool[i]) for i,k in sorted(owner.items())])
union=set().union(*(CORNERS[s] for s in pool))
supported=[t for t,c in enumerate(CORNERS) if set(c)<=union]
print('Corner-supported targets:',supported)
for t in supported:
    found=False
    for size in range(1,9):
        for req in combinations(sorted(CORNERS[t]),size):
            ns=[i for i,s in enumerate(pool) if set(req)&CORNERS[s]]
            if len(ns)<size:
                print('Target',t,'deficient corners',req,'source slots',ns)
                found=True
                break
        if found: break
    assert found
print('Other targets have an absent corner.')
