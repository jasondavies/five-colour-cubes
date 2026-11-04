"""Targeted audit of five-corner covers at a doubled opposite anchor.

No claim of exhausting smaller Hall covers with outside sources.
"""
import sys,json,time,itertools
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'root'))
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'robust_route'))
from conflict_graph import *

def allocations(total,caps):
    remaining=[0]*(len(caps)+1)
    for i in range(len(caps)-1,-1,-1):remaining[i]=remaining[i+1]+caps[i]
    x=[0]*len(caps)
    def go(i,n):
        if i==len(x):
            if n==0:yield tuple(x)
            return
        for a in range(max(0,n-remaining[i+1]),min(caps[i],n)+1):
            x[i]=a
            yield from go(i+1,n-a)
    yield from go(0,total)

def cover_orbits(size):
    target=CORNERS[60];acts=[]
    for p in itertools.permutations(V):
        for rev in (False,True):
            def tr(c,p=p,rev=rev):
                return frozenset(('t',p[b],p[a]) if rev else ('t',p[a],p[b]) for _,a,b in c)
            if tr(target)==target:acts.append(tr)
    left=set(map(frozenset,itertools.combinations(target,size)))
    out=[]
    while left:
        c=min(left,key=lambda c:sorted(c));orbit={f(c)for f in acts};left-=orbit
        out.append({'corners':sorted(c),'orbit':len(orbit),
                    'classes':[j for j in range(20)if CUTS[j]&target<=c],
                    'opps':[j for j in range(61,75)if CORNERS[j]&target<=c]})
    return out

def main(total_o):
    output=[]
    for row in cover_orbits(5):
        js,ops=row['classes'],row['opps'];start=time.monotonic()
        pairpos=[(i,k)for i,j in enumerate(js)for k,l in enumerate(js)if i<k and len(CUTS[j]&CUTS[l])==4]
        missA=[[i for i,j in enumerate(js)if CLASSES[j][0]==pair]for pair in PAIRS]
        patterns=[]
        for oo in allocations(total_o-2,[2]*len(ops)):
            os=[0]*15;os[0]=2
            for t,n in zip(ops,oo):os[t-60]=n
            missO=[sum(n for n,(r,p,q) in zip(os,OPP)if pair==p or pair==q)for pair in PAIRS]
            tested=oppfail=loopkill=cliquekill=fullkill=0;survivors=[];noclique=[];maxnodes=0
            for gg in allocations(14-total_o,[5]*len(js)):
                if any(gg[i]+gg[k]>7 for i,k in pairpos):continue
                if any(m+sum(gg[i]for i in aa)>7 for m,aa in zip(missO,missA)):continue
                tested+=1;gs=[0]*20
                for j,n in zip(js,gg):gs[j]=n
                xx=[v for g in gs for v in [g,0,0]]+os
                if solution(xx,range(60,75))is not None:continue
                oppfail+=1;G=conflict_graph(gs,os)
                if any(gs[j]>3 for j in G['loops']):loopkill+=1;continue
                clique=clique_obstruction(gs,G)
                if clique:cliquekill+=1;continue
                actual,G,nodes=find_failure_refinement(gs,os);maxnodes=max(maxnodes,nodes)
                if actual is None:fullkill+=1
                else:survivors.append({'g':gg,'refinement':actual})
                noclique.append({'g':gg,'loops':G['loops'],'edges':G['edges'],'nodes':nodes})
            patterns.append({'o':oo,'tested':tested,'oppfail':oppfail,'loopkill':loopkill,'cliquekill':cliquekill,'fullkill':fullkill,'maxnodes':maxnodes,'survivors':survivors,'noclique':noclique})
        result={**row,'total_o':total_o,'patterns':patterns,'seconds':time.monotonic()-start}
        output.append(result)
        print({**row,'total_o':total_o,'tested':sum(p['tested']for p in patterns),'oppfail':sum(p['oppfail']for p in patterns),'loopkill':sum(p['loopkill']for p in patterns),'cliquekill':sum(p['cliquekill']for p in patterns),'fullkill':sum(p['fullkill']for p in patterns),'survivors':sum(len(p['survivors'])for p in patterns),'seconds':result['seconds']},flush=True)
    dest=Path(__file__).with_name(f'double-cover-five-O{total_o}.json')
    dest.write_text(json.dumps(output,indent=2))

if __name__=='__main__':main(int(sys.argv[1])if len(sys.argv)>1 else 4)
