from pathlib import Path
import sys, argparse, json
sys.path.insert(0,str(Path(__file__).resolve().parent))
from cut_model import *
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix

def solve(n,cap,seconds,private=False,nonloop=False):
    lower=[0]*20;upper=[cap]*20;lower[0]=cap
    if private:
        for j in range(1,20):
            if ('t',0,2) in CUTS[j]:upper[j]=0
    rows=[];lo=[];hi=[]
    def add(row,l=-np.inf,u=np.inf):rows.append(row);lo.append(l);hi.append(u)
    add({i:1 for i in range(20)},n,n)
    targets=[(TARGETS[t],False)for t in range(60,75)]
    if nonloop:targets.append((tuple(CUTS[0]),True))
    for es,exclude in targets:
        witnesses={}
        for d in range(1,1<<len(es)):
            req={es[k]for k in range(len(es))if d>>k&1}
            ns=frozenset(j for j in range(20)if (j!=0 or not exclude)and CUTS[j]&req)
            b=len(req)-1
            minsum=max(sum(lower[j]for j in ns),n-sum(upper[j]for j in range(20)if j not in ns))
            if minsum<=b:witnesses[ns]=max(b,witnesses.get(ns,-1))
        kept=[(ns,b)for ns,b in witnesses.items()if not any(ns2<ns and b2>=b for ns2,b2 in witnesses.items())]
        choices=[]
        for ns,b in kept:
            z=len(lower);lower.append(0);upper.append(1);choices.append(z)
            add({**{j:1 for j in ns},z:n-b},u=n)
        add({z:1 for z in choices},l=1)
    ir=[];ic=[];vs=[]
    for i,row in enumerate(rows):
        for j,v in row.items():ir.append(i);ic.append(j);vs.append(v)
    a=coo_matrix((vs,(ir,ic)),shape=(len(rows),len(lower))).tocsc()
    print('n',n,'cap',cap,'variables',len(lower),'constraints',len(rows),flush=True)
    r=milp(np.zeros(len(lower)),integrality=np.ones(len(lower)),bounds=Bounds(lower,upper),constraints=LinearConstraint(a,lo,hi),options={'time_limit':seconds,'disp':True})
    print(r.message,flush=True)
    if r.x is not None:
        g=np.rint(r.x[:20]).astype(int).tolist();x=[n for v in g for n in [v,0,0]]+[0]*15
        print('counts',[(j,v)for j,v in enumerate(g)if v],'opposite target',solution(x,range(60,75)),flush=True)
        Path(__file__).with_name(f'low-multiplicity-{n}-{cap}.json').write_text(json.dumps(g))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=13);p.add_argument('--cap',type=int,default=2);p.add_argument('--seconds',type=float,default=40);p.add_argument('--private',action='store_true');p.add_argument('--nonloop',action='store_true');a=p.parse_args();solve(a.n,a.cap,a.seconds,a.private,a.nonloop)

