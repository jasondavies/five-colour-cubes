"""Abstract directed-cut model of five-colour corner sets (discovery only)."""
from itertools import combinations

V = frozenset(range(5))
ARCS = tuple((a,b) for a in range(5) for b in range(5) if a != b)
CUTS = tuple(frozenset(s) for k in [2,3] for s in combinations(range(5),k))
TYPES = []
CLASS = []
META = []
for j,s in enumerate(CUTS):
    poles = s if len(s)==2 else V-s
    tri_side = V-poles
    tri = frozenset(ARCS.index((a,b)) for a in s for b in V-s)
    for r in sorted(tri_side):
        TYPES.append(tri | frozenset(20+ARCS.index((r,p)) for p in poles))
        CLASS.append(j)
        META.append(('A',tuple(sorted(s)),r))
OS = []
for r in range(5):
    others = V-{r}
    a=min(others)
    for b in sorted(others-{a}):
        left=frozenset((a,b)); right=others-left
        tri=frozenset(ARCS.index((x,y)) for x in others for y in others
                      if (x in left) != (y in left))
        OS.append(tri)
        TYPES.append(tri)
        CLASS.append(-1)
        META.append(('O',r,tuple(sorted(left)),tuple(sorted(right))))
assert len(TYPES)==len(set(TYPES))==75
assert all(len(x)==8 for x in TYPES)

def fit_masks(t):
    tc=sorted(TYPES[t])
    return [sum(1<<k for k,c in enumerate(tc) if c in src) for src in TYPES]

FITS=[fit_masks(t) for t in range(75)]

def match(counts,t):
    """Small exact expanded-copy augmenting-path matching."""
    masks=[FITS[t][j] for j,n in enumerate(counts) for _ in range(n)]
    assigned=[-1]*len(masks)
    def augment(k,seen):
        for i,m in enumerate(masks):
            if m>>k&1 and i not in seen:
                seen.add(i)
                if assigned[i]<0 or augment(assigned[i],seen):
                    assigned[i]=k
                    return True
        return False
    return all(augment(k,set()) for k in range(8))

def solution(counts):
    return next((t for t in range(75) if match(counts,t)),None)

def bad_sets(counts,t):
    return [d for d in range(1,256) if sum(n for n,m in zip(counts,FITS[t]) if m&d)<d.bit_count()]

def pair_invariant(counts):
    g=[sum(counts[3*j:3*j+3]) for j in range(20)]
    o=sum(counts[60:])
    return 3*sum(n*(n-1)//2 for n in g)-4*o*(o-1)//2
