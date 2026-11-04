"""Exploratory feasibility of opposite-or-robust-cut detector failure."""
import sys, json, argparse
from pathlib import Path
from itertools import combinations
import numpy as np
from scipy.optimize import milp, Bounds, LinearConstraint
from scipy.sparse import coo_matrix
sys.path.insert(0, str(Path(__file__).resolve().parents[1]/'root'))
from cut_model import *

def solve(n=15, seconds=45, only_adjacent=False, maxg=None):
    lb=[0]*75;ub=[5]*60+[0 if only_adjacent else 4]*15
    if maxg is not None:ub[:60]=[maxg]*60
    rows=[];lo=[];hi=[]
    def add(row,l=-np.inf,u=np.inf):rows.append(row);lo.append(l);hi.append(u)
    def variable():
        z=len(lb);lb.append(0);ub.append(1);return z
    def disjunction(clauses,extra=None):
        choices=[]
        for support,bound in clauses:
            z=variable();choices.append(z)
            add({**{i:1 for i in support},z:n-bound},u=n)
        row={i:1 for i in choices}
        if extra is not None:row[extra]=1
        add(row,l=1)
    def hall_clauses(target,slack=0):
        es=sorted(target); d={}
        for mask in range(1,1<<len(es)):
            req={e for k,e in enumerate(es) if mask>>k&1}
            ns=frozenset(i for i,c in enumerate(CORNERS) if c&req and ub[i]>0)
            b=len(req)-1+slack
            d[ns]=max(b,d.get(ns,-1))
        c=list(d.items())
        return [(ns,b) for ns,b in c if not any(ns2<=ns and b2>=b and (ns2,b2)!=(ns,b) for ns2,b2 in c)]
    add({i:1 for i in range(75)},n,n)
    for j in range(20):add({i:1 for i in range(3*j,3*j+3)},u=5 if maxg is None else maxg)
    for j,k in combinations(range(20),2):
        if len(CUTS[j]&CUTS[k])==4:add({i:1 for a in [j,k] for i in range(3*a,3*a+3)},u=7)
    for p in PAIRS:
        support=[i for i,(j,r) in enumerate(ADJ) if CLASSES[j][0]==p]
        support += [60+i for i,(r,q,s) in enumerate(OPP) if p==q or p==s]
        add({i:1 for i in support},u=7)
    if maxg is not None:add({i:1 for i in range(3)},l=maxg)
    # z=1 asserts the cut is non-robust, via one Hall witness.
    for j in range(20):
        z=variable()
        disjunction(hall_clauses(CUTS[j],2),extra=z)
        # z=0 requires no bicolour matching for all repeats; z=1 robust? 
        # Above z=1 exempts nonrobust witness, so it asserts robust possibility.
        # Thus bi failure can be exempted by (1-z).
        for t in range(3*j,3*j+3):
            choices=[]
            for ns,b in hall_clauses(CORNERS[t]-CUTS[j]):
                q=variable();choices.append(q)
                add({**{i:1 for i in ns},q:n-b},u=n)
            add({**{i:1 for i in choices},z:-1},l=0)
    for t in range(60,75):disjunction(hall_clauses(CORNERS[t]))
    r=[];c=[];v=[]
    for i,row in enumerate(rows):
        for j,x in row.items():r.append(i);c.append(j);v.append(x)
    M=coo_matrix((v,(r,c)),shape=(len(rows),len(lb))).tocsc()
    print('n',n,'adjacent',only_adjacent,'variables',len(lb),'constraints',len(rows),flush=True)
    result=milp(np.zeros(len(lb)),integrality=np.ones(len(lb)),bounds=Bounds(lb,ub),constraints=LinearConstraint(M,lo,hi),options={'time_limit':seconds,'disp':True})
    print(result.message,flush=True)
    if result.x is not None:
        x=np.rint(result.x[:75]).astype(int).tolist()
        print(json.dumps({'x':x,'W':W(x),'gs':coarse(x)[0],'sources':[(i,KINDS[i],v) for i,v in enumerate(x) if v],'full_solution':solution(x)},indent=2),flush=True)
        return x

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=15);p.add_argument('--seconds',type=float,default=45);p.add_argument('--adjacent',action='store_true');p.add_argument('--maxg',type=int);a=p.parse_args()
    solve(a.n,a.seconds,a.adjacent,a.maxg)
