from replacement_geometry import *
from itertools import permutations
valid3=set()
for target in cuts+ops:
 for ss in combinations([a for a in range(20)if target>>a&1],3):valid3.add(sum(1<<a for a in ss))
print('physical corner triples',len(valid3),flush=True)
perms=[]
for p in permutations(range(5)):
 for rev in(0,1):
  perms.append([CUTS.index(frozenset(('t',p[b],p[a])if rev else('t',p[a],p[b])for _,a,b in c))for c in CUTS])
def match3(vs,tri):
 ns=[ops[v]&tri for v in vs]
 return all(ns) and all((a|b).bit_count()>=2 for a,b in combinations(ns,2)) and (ns[0]|ns[1]|ns[2]).bit_count()==3
invalid={vs:[tri for tri in valid3 if match3(vs,tri)]for vs in combinations_with_replacement(range(15),3)}
def replaceable(ss,vs):
 masks=[cuts[j]for j in ss];union=0
 for m in masks:union|=m
 if any(ops[v]&~union for v in vs):return False
 for i in range(len(ss)):
  other=0
  for j,m in enumerate(masks):
   if j!=i:other|=m
  only=masks[i]&~other
  ns=[ops[v]&only for v in vs if ops[v]&only]
  if len(ns)>=2 and (len(set(ns))>1 or ns[0].bit_count()>1):return False
 for i,j in combinations(range(len(ss)),2):
  other=0
  for k,m in enumerate(masks):
   if k not in(i,j):other|=m
  only=(masks[i]|masks[j])&~other
  if only.bit_count()>=3 and any(not tri&~only for tri in invalid[vs]):return False
 return True
seen=set();good=[];orbits=0
for ss in combinations_with_replacement(range(20),4):
 if ss in seen:continue
 orbits+=1;seen.update(tuple(sorted(p[j]for j in ss))for p in perms)
 un=0
 for j in ss:un|=cuts[j]
 cand=[v for v in range(15)if not ops[v]&~un]
 vs=[vs for vs in combinations_with_replacement(cand,3)if replaceable(ss,vs)]
 if vs:good.append((ss,vs));print('GOOD',ss,vs,flush=True)
print('orbits',orbits,'good',len(good))
seen=set();good=[];orbits=0
for ss in combinations_with_replacement(range(20),5):
 if ss in seen:continue
 orbits+=1;seen.update(tuple(sorted(p[j]for j in ss))for p in perms)
 un=0
 for j in ss:un|=cuts[j]
 cand=[v for v in range(15)if not ops[v]&~un]
 vs=[vs for vs in combinations_with_replacement(cand,3)if replaceable(ss,vs)]
 if vs:
  good.append((ss,vs));mixed=[v for v in vs if len(set(v))>1]
  print('GOOD5',ss,'options',len(vs),'mixed',mixed[:3],flush=True)
print('five orbits',orbits,'good',len(good))
