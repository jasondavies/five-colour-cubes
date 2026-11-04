import sys,itertools,json
from pathlib import Path
from collections import Counter
sys.path.insert(0,'research/root');import cut_model as m
rows=[tuple(map(int,l.split()))for l in Path('research/opposite_small_lemma/fiveO_threeA_failures.txt').read_text().splitlines()]
ps=[]
for a in itertools.permutations([0,1]):
 for b in itertools.permutations([2,3,4]):
  p=a+b;mp={i:m.CORNERS.index(frozenset(('t',p[x],p[y])for _,x,y in m.CORNERS[i]))for i in range(60,75)};ps.append(mp)
sub={r for r in rows if len(ds:=[i for i,n in Counter(r).items()if n==2])==2 and len(m.CORNERS[ds[0]]&m.CORNERS[ds[1]])==2}
reps=[]
while sub:
 r=min(sub);reps.append(r);sub-={tuple(sorted(p[i]for i in r))for p in ps}
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
