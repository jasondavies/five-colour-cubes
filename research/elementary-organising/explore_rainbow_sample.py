from replacement_geometry import *
from itertools import permutations
from random import Random
from cut_model import solution
maps=[]
for p in permutations(range(5)):
 for rev in (0,1):
  maps.append([CUTS.index(frozenset(('t',p[b],p[a]) if rev else ('t',p[a],p[b])for _,a,b in c))for c in CUTS])
seen=set();reps=[]
for a,b in combinations(range(20),2):
 if (a,b)in seen:continue
 reps.append((a,b));seen.update(tuple(sorted((m[a],m[b])))for m in maps)
print('pair reps',reps,flush=True)
rng=Random(673)
for a,b in reps:
 for n in (4,5,6,7,8):
  cores=[0]*75
  for j in(a,b):cores[3*j:3*j+3]=[1]*3
  extra=[[i]*n for i in range(75)]
  extra.extend([rng.randrange(75)for _ in range(n)]for _ in range(2000))
  bad=None
  for more in extra:
   inv=cores.copy()
   for i in more:inv[i]+=1
   if solution(inv) is None:bad=more;break
  print((a,b),'extras',n,'bad',bad,flush=True)
  if bad is None:break
