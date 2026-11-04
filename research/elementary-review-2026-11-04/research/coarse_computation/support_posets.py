from itertools import combinations,permutations
from collections import Counter
from pathlib import Path
import json
V=tuple(range(5));arcs=tuple((a,b)for a in V for b in V if a!=b);ai={e:i for i,e in enumerate(arcs)}
perms=list(permutations(V))
up=list(combinations(V,2));relations=set()
for mask in range(1<<10):
 r={(a,b)for i,(a,b) in enumerate(up)if mask>>i&1}
 if any((a,c)not in r for a,b in r for bb,c in r if b==bb):continue
 for p in perms:relations.add(frozenset((p[a],p[b])for a,b in r))
print('all partial orders',len(relations))
def noopp(r):
 inc=lambda a,b:(a,b)not in r and(b,a)not in r
 for vertices in combinations(V,4):
  a=vertices[0]
  for b in vertices[1:]:
   q=[x for x in vertices if x not in [a,b]]
   if all(inc(x,y)for x in [a,b]for y in q):return False
 return True
eligible=[r for r in relations if noopp(r)]
print('C4-free incomparability',len(eligible))
minimal=[r for r in eligible if not any(noopp(r-{edge}) for edge in r if not any((edge[0],v)in r and(v,edge[1])in r for v in V))]
print('minimal',len(minimal))
def code(r):return sum(1<<ai[e]for e in r)
def canon(r):return min(code({(p[a],p[b])for a,b in r})for p in perms)
classes={}
for r in minimal:classes.setdefault(canon(r),[]).append(r)
result=[]
for key,rs in sorted(classes.items()):
 r=rs[0]
 subsets=[S for k in [2,3] for S in combinations(V,k) if all(a not in S or b in S for a,b in r)]
 print('orbit',len(rs),'order',sorted(r),'allowed cuts',subsets)
 result.append({'count':len(rs),'relation':sorted(r),'upsets':subsets})
Path('minimal-support-posets.json').write_text(json.dumps(result,indent=2))
