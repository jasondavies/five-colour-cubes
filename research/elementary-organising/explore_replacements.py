from replacement_geometry import *
results=[]
for ss in combinations_with_replacement(range(20),3):
 masks=[cuts[i]for i in ss];un=masks[0]|masks[1]|masks[2]
 candidates=[o for o,m in enumerate(ops)if not m&~un]
 if not candidates:continue
 private=[m&~(masks[(i+1)%3]|masks[(i+2)%3])for i,m in enumerate(masks)]
 valid=[]
 for p,q in combinations_with_replacement(candidates,2):
  # Any pair of distinct required corners must have at least two actual suppliers.
  if all(not (ops[p]&h and ops[q]&h) or ((ops[p]|ops[q])&h).bit_count()<=1 for h in private):valid.append((p,q))
 if valid:results.append((ss,valid))
print('three-adjacent profiles admitting two-opposite replacement:',len(results))
print('with three distinct classes',sum(len(set(s))==3 for s,v in results))
print('with distinct opposite varieties',sum(any(p!=q for p,q in v)for s,v in results))
for s,v in results[:25]:print([CLASSES[i]for i in s],[(OPP[p],OPP[q])for p,q in v])
from itertools import permutations
perm_maps=[]
for perm in permutations(range(5)):
 for reverse in (False,True):
  tr=[]
  for c in CUTS:
   cc=frozenset(('t',perm[b],perm[a])if reverse else ('t',perm[a],perm[b])for _,a,b in c)
   tr.append(CUTS.index(cc))
  perm_maps.append(tr)
def rank_at_least(sets,k):
 if k==2:
  active=[s for s in sets if s]
  return len(active)>=2 and (len(set(active))>1 or active[0].bit_count()>1)
 if k==3:
  return all(sets) and all((a|b).bit_count()>=2 for a,b in combinations(sets,2)) and (sets[0]|sets[1]|sets[2]).bit_count()>=3
 raise ValueError(k)
def replaceable(ss,vs):
 n=len(ss);k=len(vs)
 neigh=[sum(1<<i for i,j in enumerate(ss)if cuts[j]>>a&1)for a in range(20)]
 if any(not neigh[a] and any(ops[v]>>a&1 for v in vs)for a in range(20)):return False
 for size in range(1,k):
  for subset in combinations(range(n),size):
   sm=sum(1<<i for i in subset)
   only=sum(1<<a for a,ns in enumerate(neigh)if ns and not ns&~sm)
   if not only:continue
   if rank_at_least([ops[v]&only for v in vs],size+1):return False
 return True
seen=set();reps=[]
for ss in combinations_with_replacement(range(20),4):
 if ss in seen:continue
 reps.append(ss)
 seen.update(tuple(sorted(tr[j]for j in ss))for tr in perm_maps)
print('four-adjacent orbits',len(reps))
success=[]
for ss in reps:
 union=0
 for j in ss:union|=cuts[j]
 cs=[v for v,m in enumerate(ops)if not m&~union]
 for vs in combinations_with_replacement(cs,3):
  if replaceable(ss,vs):success.append((ss,vs));break
print('4 -> 3 orbits',len(success))
for ss,vs in success[:10]:print('witness',ss,vs)
seen=set();reps5=[]
for ss in combinations_with_replacement(range(20),5):
 if ss in seen:continue
 reps5.append(ss);seen.update(tuple(sorted(tr[j]for j in ss))for tr in perm_maps)
print('five-adjacent orbits',len(reps5))
success5=[]
for ss in reps5:
 union=0
 for j in ss:union|=cuts[j]
 cs=[v for v,m in enumerate(ops)if not m&~union]
 for vs in combinations_with_replacement(cs,3):
  if replaceable(ss,vs):success5.append((ss,vs));break
print('5 -> 3 orbits',len(success5))
for ss,vs in success5[:20]:print('witness',ss,vs)
for ss,first in success5:
 cs=[v for v in range(15)if not ops[v]&~(__import__('functools').reduce(int.__or__,(cuts[j]for j in ss),0))]
 valid=[vs for vs in combinations_with_replacement(cs,3)if replaceable(ss,vs)]
 mixed=[vs for vs in valid if len(set(vs))>1]
 print('5->3 full',ss,'options',len(valid),'distinct',len(mixed),mixed[:2])
from cut_model import solution
counts=[0]*75;counts[60]=5;counts[67]=3
print('5O60+3O67 target',solution(counts))
