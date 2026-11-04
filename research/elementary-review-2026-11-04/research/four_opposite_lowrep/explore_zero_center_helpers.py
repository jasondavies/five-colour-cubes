from itertools import combinations
from pathlib import Path
import json,sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'root'))
from cut_model import CUTS,CORNERS

def match(S,P):
 P=list(P);owner=[-1]*len(S)
 def aug(k,seen):
  for i,s in enumerate(S):
   if i in seen or P[k]not in s:continue
   seen.add(i)
   if owner[i]<0 or aug(owner[i],seen):owner[i]=k;return True
  return False
 return all(aug(k,set())for k in range(len(P)))

out=[]
for aj in (14,16):
 core=[CORNERS[t]for t in (60,60,64,68)]+[CUTS[aj]]*2
 helpers=[j for j,c in enumerate(CUTS)if j!=aj and ('t',1,2)not in c]
 pairs=list(combinations(helpers,2))
 masks=[];data=[]
 for t in range(60,75):
  T=CORNERS[t];holes=[p for p in combinations(T,2)if match(core,T-set(p))]
  solved=[]
  for k,(b,c)in enumerate(pairs):
   if any((x in CUTS[b]and y in CUTS[c])or(y in CUTS[b]and x in CUTS[c])for x,y in holes):solved.append(k)
  masks.append(sum(1<<k for k in solved))
  data.append({'target':t,'holes':[[f'{x[1]}{x[2]}'for x in p]for p in holes],'solved':len(solved),'fail':[pairs[k]for k in range(len(pairs))if k not in solved]})
 full=(1<<len(pairs))-1;cover=None
 for n in range(1,5):
  for inds in combinations(range(15),n):
   mask=0
   for i in inds:mask|=masks[i]
   if mask==full:cover=inds;break
  if cover is not None:break
 out.append({'A':aj,'helpers':helpers,'npairs':len(pairs),'cover':None if cover is None else[x+60 for x in cover],'details':[data[i]for i in cover or []]})
print(json.dumps(out,indent=2))
Path(__file__).with_name('zero-center-helper-targets.json').write_text(json.dumps(out,indent=2)+'\n')
