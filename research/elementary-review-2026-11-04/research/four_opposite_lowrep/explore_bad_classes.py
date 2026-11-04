from itertools import combinations,permutations
from pathlib import Path
import json,sys,collections
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'root'))
from cut_model import CUTS,CORNERS
O=list(CORNERS[60:]);V=range(5)
def relabel(s,p):return frozenset((t,p[a],p[b]) for t,a,b in s)
trans=[[O.index(relabel(s,p)) for s in O]for p in permutations(V)]
def canon(inv):return min(tuple(sorted(p[j]for j in inv)) for p in trans)
cores=set()
for xs in combinations(range(15),4):cores.add(canon(xs))
for d in range(15):
 for ss in combinations([j for j in range(15)if j!=d],2):cores.add(canon((d,d)+ss))
def match(S,P):
 P=list(P);owner=[-1]*len(S)
 def aug(k,seen):
  for i,s in enumerate(S):
   if i in seen or P[k] not in s:continue
   seen.add(i)
   if owner[i]<0 or aug(owner[i],seen):owner[i]=k;return True
  return False
 return all(aug(k,set())for k in range(len(P)))
rows=[]
for inv in sorted(cores):
 sources=[O[j]for j in inv]
 good=[t for t in range(15)if match(sources,[c for c in O[t]if c[1]<c[2]])]
 bad=[j for j,c in enumerate(CUTS)if all(len(c&O[t])<4 for t in good)]
 rows.append({'opposite':[j+60 for j in inv],'good_targets':[j+60 for j in good],'bad_classes':bad})
print(json.dumps(rows,indent=2))
Path(__file__).with_name('bad-classes.json').write_text(json.dumps(rows,indent=2)+'\n')
