"""Discover small geometric Hall tables, not an inventory proof."""
from itertools import combinations
import json,sys
sys.path.insert(0,'research/root')
from cut_model import CUTS,CORNERS,TARGETS

CORES=[(0,1,2,15,19),(0,2,5,7,8),(0,2,5,8,19),
       (0,2,5,11,16),(0,2,5,13,19)]

def constraints(core,t):
    helpers=set(range(20))-set(core)
    out={}
    for n in range(1,9):
        for pos in combinations(TARGETS[t],n):
            S=frozenset(pos)
            a=2*sum(bool(CUTS[j]&S) for j in core)
            k=n-1-a
            if k<0:continue
            D=frozenset(j for j in helpers if not CUTS[j]&S)
            if len(D)<3-k:continue
            key=(D,k)
            out.setdefault(key,S)
    # A smaller |D|+k obstruction is stronger, and dominated by a larger one.
    keys=list(out)
    keep=[]
    for i,(D,k) in enumerate(keys):
        if any((len(D-E)+k<=l) and (len(E-D)+l>k or j<i)
               for j,(E,l) in enumerate(keys) if j!=i):continue
        keep.append((D,k,out[(D,k)]))
    return keep

def possible_failure(H,rows):
    return any(len(set(H)-D)<=k for D,k,S in rows)

report=[]
for core in CORES:
    hs=list(combinations(set(range(20))-set(core),3))
    ts={t:constraints(core,t) for t in range(60,75)}
    good={t:{H for H in hs if not possible_failure(H,rows)}
          for t,rows in ts.items()}
    chosen=None
    for n in range(1,5):
        opts=[]
        for targets in combinations(range(60,75),n):
            if len(set.union(*(good[t] for t in targets)))==len(hs):
                opts.append((sum(len(ts[t]) for t in targets),targets))
        if opts:chosen=min(opts)[1];break
    rows=[]
    for t in chosen:
        rows.append({'target':t,'conditions':[
            {'D':sorted(D),'k':k,'S':[[a,b] for _,a,b in sorted(S)]}
            for D,k,S in ts[t]]})
    report.append({'core':core,'tables':rows})
print(json.dumps(report,indent=2))
