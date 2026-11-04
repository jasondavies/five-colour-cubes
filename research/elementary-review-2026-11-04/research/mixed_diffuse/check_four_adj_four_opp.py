import sys,json,itertools,time
from pathlib import Path
from check_double_covers import *

def cases():
    a=CUTS[0];actions=[]
    for p in itertools.permutations(V):
        def tr(c,p=p):return frozenset(('t',p[x],p[y])for _,x,y in c)
        if tr(a)==a:
            perm=[CORNERS.index(tr(c))for c in CORNERS[60:]]
            actions.append((tr,perm))
    left=set(map(frozenset,itertools.combinations(a,3)));result=[]
    while left:
        h=min(left,key=lambda h:sorted(h));orbit={tr(h)for tr,p in actions};left-=orbit
        ops=[o for o in range(60,75)if CORNERS[o]&a<=h]
        js=[j for j in range(20)if CUTS[j]&a<=h]
        sub=[p for tr,p in actions if tr(h)==h]
        inventories=set()
        for oo in allocations(4,[2]*len(ops)):
            x=[0]*15
            for o,n in zip(ops,oo):x[o-60]=n
            if len(set().union(*(CORNERS[60+o]&a for o,n in enumerate(x)if n)))!=3:continue
            images=[]
            for p in sub:
                y=[0]*15
                for o,n in enumerate(x):y[p[o]-60]=n
                images.append(tuple(y))
            inventories.add(min(images))
        for os in sorted(inventories):result.append({'H':sorted(h),'classes':js,'os':os})
    return result

def main():
    out=[]
    for row in cases():
        start=time.monotonic();js=row['classes'];os=row['os'];tested=0;F=[];N=[];none=0;loop=0;clique=0
        for gg in allocations(6,[4]*len(js)):
            gs=[0]*20;gs[0]=4
            for j,n in zip(js,gg):gs[j]=n
            if any(gs[j]+gs[k]>7 for j in range(20)for k in range(j)if len(CUTS[j]&CUTS[k])==4):continue
            if any(sum(gs[j]for j in range(20)if CLASSES[j][0]==pair)+sum(n for n,(r,p,q)in zip(os,OPP)if pair==p or pair==q)>7 for pair in PAIRS):continue
            tested+=1;x=[v for g in gs for v in [g,0,0]]+list(os)
            if solution(x,range(60,75))is not None:continue
            G=conflict_graph(gs,os)
            if any(gs[j]>3 for j in G['loops']):loop+=1;continue
            cl=clique_obstruction(gs,G)
            if cl:clique+=1;F.append({'g':gg,'loops':G['loops'],'clique':cl});continue
            fail,G,nodes=find_failure_refinement(gs,os)
            if fail is not None:raise AssertionError(fail)
            N.append({'g':gg,'loops':G['loops'],'edges':G['edges'],'nodes':nodes})
        result={**row,'tested':tested,'loopkill':loop,'cliquekill':clique,'noclique':N,'cliquecases':F,'seconds':time.monotonic()-start}
        out.append(result);print({k:v for k,v in result.items()if k not in ['noclique','cliquecases']}|{'noclique':len(N)},flush=True)
    Path(__file__).with_name('four-adj-four-opp.json').write_text(json.dumps(out,indent=2))
if __name__=='__main__':main()
