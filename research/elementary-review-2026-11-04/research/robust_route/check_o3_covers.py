import json,sys,time
from pathlib import Path
from itertools import combinations
from collections import Counter
from conflict_graph import *

def allocations(bounds,total):
    caps=[0]*(len(bounds)+1)
    for i in range(len(bounds)-1,-1,-1):caps[i]=caps[i+1]+bounds[i]
    x=[0]*len(bounds)
    def rec(i,rem):
        if i==len(bounds):
            if rem==0:yield tuple(x)
            return
        for n in range(max(0,rem-caps[i+1]),min(rem,bounds[i])+1):
            x[i]=n;yield from rec(i+1,rem-n)
    yield from rec(0,total)

if __name__=='__main__':
    wanted=set(map(int,sys.argv[1:]))or{23,27,30,51,53,54,102}
    rows=json.loads(Path('research/invariant_structure/o3_covers.json').read_text())
    output=[]
    for row in rows:
        if row['mask']not in wanted or row['size']!=4:continue
        js=row['classes'];ops=row['opps'];bounds=[5]*len(js)+[3]*len(ops)
        pairs=[(a,b)for a,b in combinations(js,2)if len(CUTS[a]&CUTS[b])==4]
        tested=0;oc=0;F=[];examples=[];start=time.monotonic();maxnodes=0;cliques=Counter();no_cliques=[]
        for x in allocations(bounds,11):
            gs=[0]*20;os=[0]*15;os[0]=3
            for j,n in zip(js,x):gs[j]=n
            for t,n in zip(ops,x[len(js):]):os[t-60]=n
            if any(gs[a]+gs[b]>7 for a,b in pairs):continue
            if any(sum(gs[j]for j in range(20)if CLASSES[j][0]==p)+sum(os[i]for i,(r,q,s)in enumerate(OPP)if p==q or p==s)>7 for p in PAIRS):continue
            tested+=1
            representative=[v for g in gs for v in [g,0,0]]+os
            if solution(representative,range(60,75))is not None:continue
            oc+=1
            xx,G,nodes=find_failure_refinement(gs,os);maxnodes=max(maxnodes,nodes)
            clique=clique_obstruction(gs,G)
            if clique is not None:
                cliques[str((tuple(clique['clique']),clique['weight'],tuple(clique['common_poles'])))]+=1
            elif xx is None:no_cliques.append({'counts':x,'loops':G['loops'],'edges':G['edges']})
            if len(examples)<30:
                examples.append({'counts':x,'loops':G['loops'],'edges':G['edges'],'nodes':nodes,'failing':xx is not None,'clique':clique})
            if xx is not None:F.append({'counts':x,'refinement':xx})
        out={'mask':row['mask'],'classes':js,'opps':ops,'tested':tested,'opp_fail':oc,'failures':F,'examples':examples,'max_nodes':maxnodes,'seconds':time.monotonic()-start,'cliques':dict(cliques),'no_cliques':no_cliques}
        output.append(out);print(json.dumps({k:v for k,v in out.items()if k not in ['examples','cliques','no_cliques','failures']}|{'failure_count':len(F),'no_clique_count':len(no_cliques),'clique_count':sum(cliques.values())}),flush=True)
    dest=Path('research/robust_route/o3_cover_results.json')
    old=json.loads(dest.read_text())if dest.exists()else[]
    keep={row['mask']:row for row in old}
    keep.update({row['mask']:row for row in output})
    dest.write_text(json.dumps(list(keep.values()),indent=2))
