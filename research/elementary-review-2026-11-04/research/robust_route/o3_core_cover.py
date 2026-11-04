import sys,json
from itertools import combinations
from collections import Counter
from check_o3_covers import allocations
from conflict_graph import *

def core_cover(mask):
    row=next(row for row in json.load(open('research/invariant_structure/o3_covers.json')) if row['size']==4 and row['mask']==mask)
    js=row['classes'];ops=row['opps'];bounds=[3]+[5]*len(js)+[3]*len(ops)
    def physical(x):
        z=[0]*75;z[60]=x[0]
        for j,n in zip(js,x[1:]):z[3*j]=n
        for o,n in zip(ops,x[1+len(js):]):z[o]=n
        return z
    def caps(x):
        z=physical(x);gs,os=coarse(z)
        if any(gs[j]+gs[k]>7 for j,k in combinations(js,2)if len(CUTS[j]&CUTS[k])==4):return False
        if any(sum(gs[j]for j in js if CLASSES[j][0]==p)+sum(os[i]for i,(r,q,s)in enumerate(OPP)if p==q or p==s)>7 for p in PAIRS):return False
        return True
    allp=[];fail=[]
    for xx in allocations(bounds[1:],11):
        x=(3,)+xx
        if not caps(x):continue
        if solution(physical(x),range(60,75))is not None:allp.append(x)
        else:fail.append(x)
    cs=[]
    for x in allocations(bounds,8):
        t=solution(physical(x),range(60,75))
        if t is None:continue
        cover=sum(1<<i for i,y in enumerate(allp)if all(a<=b for a,b in zip(x,y)))
        if cover:cs.append((x,t,cover))
    uncovered=(1<<len(allp))-1;chosen=[]
    while uncovered:
        x,t,cov=max(cs,key=lambda q:(q[2]&uncovered).bit_count())
        n=(cov&uncovered).bit_count();assert n
        chosen.append({'core':x,'target':t,'newly_covered':n});uncovered&=~cov
    result={'mask':mask,'class_order':['O60']+js+ops,'soluble_count':len(allp),'failure_count':len(fail),'available_cores':len(cs),'chosen':chosen}
    print(json.dumps(result,indent=2),flush=True)
    Path(f'research/robust_route/o3_core_cover_{mask}.json').write_text(json.dumps(result,indent=2))
    return result

if __name__=='__main__':
    for arg in sys.argv[1:]:core_cover(int(arg))
