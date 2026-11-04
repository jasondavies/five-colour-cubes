"""Discovery of small Hall inequality certificates; no inventory theorem claimed."""
import sys,itertools,json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'root'))
from cut_model import *

FAMILIES={
    'rectangle':[0,15,6,12,19,17],
    'diamond':[2,4,6,9,11,13],
    'chain':[6,2,11,19],
}
def rows(os,js,t,total=11):
    out=set()
    for mask in range(1,256):
        a=sum(bool(MASKS[t][o]&mask) for o in os)
        k=mask.bit_count()-1-a
        if k<0:continue
        E=sum(1<<i for i,j in enumerate(js) if MASKS[t][3*j]&mask)
        if 3*(len(js)-E.bit_count())+k<total:continue
        out.add((E,k))
    # Keep weakest sufficient obstructions; E,k => F,l if k+3|F\E|<=l.
    rr=[]
    for E,k in out:
        if any((E,k)!=(F,l) and k+3*(F&~E).bit_count()<=l for F,l in out):continue
        rr.append((E,k))
    return sorted(rr)
def maxmass(m,ineq):
    # This small bound enumerates only group totals under displayed linear rows.
    best=0
    for g in itertools.product(range(4),repeat=m):
        if all(sum(x for i,x in enumerate(g) if E>>i&1)<=k for E,k in ineq):
            best=max(best,sum(g))
    return best
def main():
    T=72
    high=[o for o in range(60,75) if len(CORNERS[o]&CORNERS[T])>=4]
    for name,js in FAMILIES.items():
        print('FAMILY',name,js)
        stat={}
        hard=[]
        for os in itertools.combinations(high,3):
            rr={t:rows(os,js,t) for t in range(60,75)}
            always=[t for t,r in rr.items() if not r]
            if always:stat['one']=stat.get('one',0)+1;continue
            pairs=[]
            for a,b in itertools.combinations(rr,2):
                if all(maxmass(len(js),[x,y])<11 for x in rr[a] for y in rr[b]):pairs.append((a,b))
            if pairs:stat['two']=stat.get('two',0)+1
            else:hard.append((os,{t:r for t,r in rr.items() if (0,0) not in r}))
        print('STAT',stat,'HARD',len(hard))
        print(json.dumps(hard))
if __name__=='__main__':main()
