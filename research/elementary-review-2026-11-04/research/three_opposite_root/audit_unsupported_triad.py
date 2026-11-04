"""Independent small-geometry audit of the displayed unsupported-triad proof.

Checks corner-set Hall implications and finite set intersections, never
source multiplicity inventories or repeated-colour refinements.
"""
import sys,json
from pathlib import Path
from itertools import combinations
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'root'))
from cut_model import CUTS,CORNERS,V

def arc(s):return ('t',int(s[0]),int(s[1]))
def cut(s):
    side={int(c) for c in s}
    return frozenset(('t',a,b)for a in side for b in V if b not in side)
allowed={c for c in CUTS if arc('12')not in c}
rawP=[
('a','31,42',0,'02,124,123,12,024,24,012'),
("a'",'13,24',0,'234,03,04,034,024,24,34'),
('b','13,42',0,'234,02,03,123,024,023,23,24'),
('c','13,31,42',1,'02,123,024,24'),
("c'",'13,24,42',1,'234,03,024,24'),
('d','13,23,32,42',1,'234,123,023,23'),
("d'",'13,14,41,42',1,'02,03,023,23')]
rawQ=[
('A','02,40',0,'02,123,12,024,023,23,012'),
('B','20,40',0,'02,03,04,034,024,023,012'),
('C','02,04',0,'234,124,123,12,024,23,24,34'),
('D','02,20,40',1,'02,024,023,012'),
('E','02,04,40',1,'123,12,024,23')]
def prepare(raw):
    return [(name,{arc(s)for s in zs.split(',')},k,{cut(s)for s in ds.split(',')})for name,zs,k,ds in raw]
P,Q=prepare(rawP),prepare(rawQ)
perm=(0,2,1,4,3)
def sigma(s):return frozenset(('t',perm[b],perm[a])for _,a,b in s)
R=[(name,sigma(z),k,{sigma(c)for c in ds})for name,z,k,ds in Q]
core=(60,64,68)
counts={}
for t,rows in zip(core,(P,Q,R)):
    target=CORNERS[t]
    for name,z,k,ds in rows:
        assert z<=target
        assert k==len(z)-1-sum(bool(z&CORNERS[o])for o in core)
        assert ds=={c for c in allowed if not(c&z)}
    ordinary=discarded=implied=0
    for n in range(1,9):
        for zz in combinations(target,n):
            z=set(zz)
            k=n-1-sum(bool(z&CORNERS[o])for o in core)
            ds={c for c in allowed if not(c&z)}
            if k<0 or 3*len(ds)+k<11:
                ordinary+=1;continue
            full=sum(arc(str(a)+str(b))in z and arc(str(b)+str(a))in z for a,b in combinations(V,2))
            common=set.intersection(*(set(c)for c in ds))if ds else set()
            if (k==0 and full>=1)or(k<=2 and full>=2)or(k==0 and common):
                discarded+=1;continue
            assert any(ds<=dr and k<=kr for name,zr,kr,dr in rows),(t,z,k,ds)
            implied+=1
    counts[t]={'automatic':ordinary,'solved_discard':discarded,'implied_by_displayed_row':implied}
table=[]
for _,_,kq,dq in Q:
    line=[]
    for _,_,kr,dr in R:
        m=tuple(max(len(dp&dq&dr)for _,_,kp,dp in P if kp==v)for v in (0,1))
        line.append(m)
        for _,_,kp,dp in P:
            assert len(dp&dq&dr)<=4-kp-kq-kr
    table.append(line)
expected=[[(2,2),(2,2),(3,2),(1,1),(1,1)],
          [(2,2),(0,0),(4,3),(0,0),(2,2)],
          [(3,2),(4,3),(2,2),(3,2),(1,1)],
          [(1,1),(0,0),(3,2),(0,0),(1,1)],
          [(1,1),(2,2),(1,1),(1,1),(0,0)]]
assert table==expected
large=[]
for np,zp,kp,dp in P:
    for nq,zq,kq,dq in Q:
        for nr,zr,kr,dr in R:
            if kp+kq+kr:continue
            inter=dp&dq&dr
            if len(inter)>=4:
                common=set.intersection(*(set(c)for c in inter))
                assert common
                large.append((np,nq,nr,sorted(common)))
report={'status':'passed','corner_sets_per_target':255,'targets':counts,
        'displayed_intersection_table_verified':True,'large_zero_bound_intersections':large}
Path(__file__).with_name('unsupported-triad-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
