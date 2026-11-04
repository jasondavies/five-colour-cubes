from pathlib import Path
import sys,json
from itertools import combinations,combinations_with_replacement,permutations
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'elementary-review-2026-11-04/research/root'))
from cut_model import *
core=[0,1,2,45,46,47]
extras=[18,21,36,39,50,53,56,59]+list(range(60,75))
def match(pool,req):
 ns=sorted(([i for i,s in enumerate(pool)if c in CORNERS[s]]for c in req),key=len)
 owners=[-1]*len(pool)
 def aug(j,seen):
  for i in ns[j]:
   if i in seen:continue
   seen.add(i)
   if owners[i]<0 or aug(owners[i],seen):owners[i]=j;return True
  return False
 return all(aug(j,set())for j in range(len(ns)))
def loop(x,j):
 pool=core+list(x)
 for _ in range(2):pool.remove(next(s for s in pool if s//3==j))
 return match(pool,CUTS[j])
pairs=list(combinations_with_replacement(extras,2))
pa={p for p in pairs if loop(p,0)};pc={p for p in pairs if loop(p,15)}
common=pa&pc
print('pair witnesses',len(pa),len(pc),'common',len(common))
no_common=[]
for n in (3,4):
 for x in combinations_with_replacement(extras,n):
  ps=set(combinations(x,2))
  if ps&common or not ps&pa or not ps&pc:continue
  # Omit supersets of shorter configurations.
  if n==4 and any(set(combinations(y,2))&pa and set(combinations(y,2))&pc for y in combinations(x,3)):continue
  inv=[0]*75
  for s in core+list(x):inv[s]+=1
  t=solution(inv)
  no_common.append({'extras':x,'target':t})
  if t is None:print('UNSOLVED',x)
print('minimal pairs-without-common-pair',len(no_common),'unsolved',sum(r['target']is None for r in no_common))
print(no_common[:20])
Path('research/elementary-organising/common-witness-probe.json').write_text(json.dumps({'A_pairs':sorted(pa),'C_pairs':sorted(pc),'common_pairs':sorted(common),'minimal_no_common_configs':no_common},indent=2)+'\n')
