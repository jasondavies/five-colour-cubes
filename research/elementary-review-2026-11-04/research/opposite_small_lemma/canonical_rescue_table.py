import sys,itertools,json
from pathlib import Path
from collections import Counter
sys.path.insert(0,'research/root');import cut_model as m
reps=[]
for p,q,cs in [(65,73,[61,63,64,68,69,70,71]),(65,70,[63,64,73]),(61,65,[68,71,73]),(71,73,[61,65,68])]:
 for c in cs:reps.append((p,p,q,q,c))
def matching(cs,S):
 owner=[None]*len(cs)
 def aug(c,seen):
  for j,s in enumerate(cs):
   if j not in seen and c in m.CORNERS[s]:
    seen.add(j)
    if owner[j] is None or aug(owner[j],seen):owner[j]=c;return True
  return False
 if all(aug(c,set())for c in S):return owner
for row in reps:
 cs=list(row)+[0]*3;es=[]
 for t in range(60,75):
  E={c for c in m.CORNERS[t]if matching(cs,m.CORNERS[t]-{c})}
  if E:es.append((t,E))
 options=[]
 for k in range(1,len(es)+1):
  for choice in itertools.combinations(es,k):
   U=set().union(*(E for _,E in choice));avoid=[j for j,c in enumerate(m.CUTS)if not(c&U)]
   if len(avoid)<=2:options.append((sum(len(E)for _,E in choice),choice,avoid))
  if options:break
 _,choice,avoid=min(options,key=lambda v:v[0])
 print(row,'choice',[(t,tuple(sorted((a,b)for _,a,b in E)))for t,E in choice],'avoid',avoid)
