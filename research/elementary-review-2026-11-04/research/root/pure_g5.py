from pathlib import Path
import sys,json,itertools,time
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'robust_route'))
from conflict_graph import *

def allocations(total,bounds):
    if not bounds:
        if total==0:yield()
        return
    for n in range(max(0,total-sum(bounds[1:])),min(total,bounds[0])+1):
        for rest in allocations(total-n,bounds[1:]):yield(n,)+rest

def inspect(family,eligible,total,extra=None):
    caps=[min(3 if not CUTS[j]&CUTS[0] else 5,2 if len(CUTS[j]&CUTS[0])==4 else 5)for j in eligible]
    if 1 in eligible:caps[eligible.index(1)]=2
    raw=oppfail=pairfail=graphfail=0;patterns=[];maxnodes=0;start=time.monotonic()
    for vv in allocations(total,caps):
        gs=[0]*20;gs[0]=5
        for j,n in zip(eligible,vv):gs[j]+=n
        if extra is not None:gs[extra]+=1
        if any(g>5 for g in gs):continue
        if any(gs[j]+gs[k]>7 for j,k in itertools.combinations(range(20),2)if len(CUTS[j]&CUTS[k])==4):continue
        if any(gs[2*i]+gs[2*i+1]>7 for i in range(10)):continue
        raw+=1
        x=[n for g in gs for n in [g,0,0]]+[0]*15
        if solution(x,range(60,75)) is not None:continue
        oppfail+=1
        G=conflict_graph(gs)
        if any(gs[j]>=4 for j in G['loops']):continue
        pairfail+=1
        tri=set().union(*(CUTS[j] for j,g in enumerate(gs)if g))
        support=[o for o in range(60,75)if CORNERS[o]<=tri]
        xx,GG,nodes=find_failure_refinement(gs);maxnodes=max(maxnodes,nodes)
        if xx is not None:graphfail+=1
        patterns.append({'g':[(j,g)for j,g in enumerate(gs)if g], 'loops':G['loops'],'edges':G['edges'],'supportedO':support,'clique':clique_obstruction(gs,G),'failure':xx,'nodes':nodes})
    out={'family':family,'eligible':eligible,'extra':extra,'raw':raw,'oppfail':oppfail,'after_loop4':pairfail,'failure_count':graphfail,'maxnodes':maxnodes,'seconds':time.monotonic()-start,'patterns':patterns}
    print(json.dumps({k:v for k,v in out.items()if k!='patterns'}),flush=True)
    return out

if __name__=='__main__':
    mode=sys.argv[1]if len(sys.argv)>1 else'all';results=[]
    if mode in ('all','pairs'):
        for name,C in [('row',[(1,3),(1,4)]),('column',[(0,3),(1,3)]),('diagonal',[(0,3),(1,4)])]:
            c={('t',a,b)for a,b in C};eligible=[j for j in range(1,20)if CUTS[j]&CUTS[0]<=c]
            results.append(inspect(name,eligible,9))
    if mode in ('all','exception'):
        c={('t',1,3)};eligible=[j for j in range(1,20)if CUTS[j]&CUTS[0]<=c]
        for extra in range(1,20):
            if extra in eligible:continue
            results.append(inspect('one-corner-plus-exception',eligible,8,extra))
    Path(__file__).with_name('pure-g5-'+mode+'.json').write_text(json.dumps(results,indent=2))

