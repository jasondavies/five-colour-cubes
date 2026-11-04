"""Small geometric Hall-table exploration for the unsupported triad."""
import sys,itertools,json
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'root'))
from cut_model import *
OS=(60,64,68)
JS=[j for j in range(20) if ('t',1,2) not in CUTS[j]]
FULL=(1<<len(JS))-1
def label(j):
    p,s=CLASSES[j]
    return ''.join(map(str,p if s==1 else [v for v in V if v not in p]))
def rows(t):
    out={}
    for mask in range(1,256):
        S=[TARGETS[t][k] for k in range(8) if mask>>k&1]
        a=sum(bool(MASKS[t][o]&mask) for o in OS)
        k=mask.bit_count()-1-a
        if k<0:continue
        E=sum(1<<i for i,j in enumerate(JS) if MASKS[t][3*j]&mask)
        D=FULL^E
        if 3*D.bit_count()+k<11:continue
        edges=[(a,b) for a in V for b in V if a<b and ('t',a,b) in S and ('t',b,a) in S]
        if k==0 and edges:continue  # global adjacent-zero edge
        if k<=2 and len(edges)>=2:continue # nine avoid two edges
        common=set.intersection(*(set(CUTS[j]) for i,j in enumerate(JS) if D>>i&1)) if D else set()
        if k==0 and common:continue # common-corner eleven
        out.setdefault((E,k),S)
    rr={}
    for (E,k),S in out.items():
        if any((E,k)!=(F,l) and k+3*(F&~E).bit_count()<=l for F,l in out):continue
        rr[E,k]=S
    return rr
def main():
    rr={t:rows(t) for t in OS}
    print('Allowed classes:',[(j,label(j)) for j in JS])
    for t,rows_t in rr.items():
        print('\nTARGET',t,'ROWS',len(rows_t))
        for i,((E,k),S) in enumerate(sorted(rows_t.items())):
            print(i,'S',' '.join(str(a)+str(b) for _,a,b in S),'k',k,'D',[label(j) for z,j in enumerate(JS) if not E>>z&1])
    combos=[]
    for inds in itertools.product(*(range(len(rr[t])) for t in OS)):
        chosen=[sorted(rr[t])[i] for t,i in zip(OS,inds)]
        D=FULL
        for E,k in chosen:D &= FULL^E
        bound=3*D.bit_count()+sum(k for E,k in chosen)
        if bound<11:continue
        common=set.intersection(*(set(CUTS[j]) for i,j in enumerate(JS) if D>>i&1)) if D else set()
        if common and all(k==0 for E,k in chosen):continue
        combos.append((inds,bound,[label(j) for i,j in enumerate(JS) if D>>i&1],chosen))
    print('Surviving crude combos',len(combos))
    for c in combos:print(c)
if __name__=='__main__':main()
