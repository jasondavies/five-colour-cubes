from coarse_milp import arcs,cuts,matching
import numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import coo_matrix
import argparse,json

def solve(n=11,limit=45,maxg=None,margin=0):
    lb=[0]*20;ub=[5+margin]*20;rows=[];lo=[];hi=[]
    if maxg is not None:
        lb[0]=maxg;ub=[maxg]*20
    def add(row,l=-np.inf,u=np.inf):rows.append(row);lo.append(l);hi.append(u)
    add({i:1 for i in range(20)},n,n)
    for t in range(20):
        es=sorted(arcs[t]); ds={}
        for mask in range(1,64):
            req={e for i,e in enumerate(es) if mask>>i&1}
            ns=frozenset(i for i in range(20) if arcs[i]&req)
            ds[ns]=max(ds.get(ns,-1),len(req)-1+margin)
        retained=[(ns,b) for ns,b in ds.items() if not any(ns2<=ns and b2>=b and ns2!=ns for ns2,b2 in ds.items())]
        choices=[]
        for ns,b in retained:
            z=len(lb);lb.append(0);ub.append(1);choices.append(z)
            add({**{i:1 for i in ns},z:n-b},u=n)
        add({z:1 for z in choices},l=1)
    ir=[];ic=[];v=[]
    for r,row in enumerate(rows):
        for c,x in row.items():ir.append(r);ic.append(c);v.append(x)
    a=coo_matrix((v,(ir,ic)),shape=(len(rows),len(lb))).tocsc()
    print('n',n,'maxg',maxg,'vars',len(lb),'constraints',len(rows),flush=True)
    result=milp(np.zeros(len(lb)),integrality=np.ones(len(lb)),bounds=Bounds(lb,ub),constraints=LinearConstraint(a,lo,hi),options={'disp':True,'time_limit':limit})
    print(result.message,flush=True)
    if result.x is not None:
        x=np.rint(result.x[:20]).astype(int).tolist()
        if not margin:assert not any(matching(x+[0]*15,t) for t in range(20))
        out={'n':n,'x':x,'g':{str(sorted(cuts[i])):v for i,v in enumerate(x) if v}}
        print(json.dumps(out,indent=2),flush=True);return out
    return None

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=11);p.add_argument('--maxg',type=int);p.add_argument('--seconds',type=float,default=45);p.add_argument('--margin',type=int,default=0);a=p.parse_args();solve(a.n,a.seconds,a.maxg,a.margin)
