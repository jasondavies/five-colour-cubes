#!/usr/bin/env python3
"""Independent geometry and search for the nested two-rainbow core.

This does not import the supplied corner model or the C++ mask table.
Failure witnesses are also checked by Hall's inequalities. Own completions
are checked by all 63 nonempty subsets, independently of the C++ matcher.
"""
from itertools import combinations
from pathlib import Path
import json,time

V=frozenset(range(5));sources=[];classes=[]
for poles in combinations(range(5),2):
 for side in (frozenset(poles),V-frozenset(poles)):
  tri=frozenset(('t',a,b) for a in side for b in V-side)
  classes.append(tri)
  for r in sorted(V-frozenset(poles)):
   sources.append(tri|frozenset(('b',r,p)for p in poles))
for r in range(5):
 other=sorted(V-{r})
 for b in other[1:]:
  left={other[0],b};right=V-left-{r}
  sources.append(frozenset(('t',a,b)for l,q in ((left,right),(right,left))for a in l for b in q))
assert len(sources)==len(set(sources))==75
positions=[sorted(t) for t in sources]
neighbors=[[[s for s in range(75)if c in sources[s]]for c in p]for p in positions]
core=(0,1,2,45,46,47)
nodes=[0]*14;failures=[];pruned=0;started=time.monotonic()

def matching(pool,target):
 ns=sorted(([i for i,s in enumerate(pool)if c in sources[s]]for c in positions[target]),key=len)
 if not ns[0]:return False
 owner=[-1]*len(pool)
 def augment(k,seen):
  for i in ns[k]:
   if i in seen:continue
   seen.add(i)
   if owner[i]<0 or augment(owner[i],seen):owner[i]=k;return True
  return False
 return all(augment(k,set()) for k in range(8))

def hall(pool,requirements):
 ns=[sum(1<<i for i,s in enumerate(pool)if c in sources[s])for c in sorted(requirements)]
 unions=[0]*(1<<len(ns))
 for mask in range(1,len(unions)):
  bit=mask&-mask;unions[mask]=unions[mask^bit]|ns[bit.bit_length()-1]
  if unions[mask].bit_count()<mask.bit_count():return False
 return True

def loop(pool,j):
 remaining=list(pool)
 for _ in range(2):
  k=next(i for i,s in enumerate(remaining)if s<60 and s//3==j)
  del remaining[k]
 return hall(remaining,classes[j])

def search(pool,lower):
 global pruned
 nodes[len(pool)]+=1
 if len(pool)>=8 and any(matching(pool,t)for t in list(range(60,75))+list(range(60))):
  pruned+=1;return
 if len(pool)==13:
  assert not any(hall(pool,t) for t in sources)
  loops=[loop(pool,j)for j in (0,15)]
  assert not all(loops),(pool,loops)
  pair_hits=[any(sources[s] & pair for s in pool[6:]) for pair in ({('t',0,4),('t',1,4)}, {('t',4,2),('t',4,3)})]
  assert not all(pair_hits), (pool, pair_hits)
  failures.append({'extra_sources':pool[6:],'own_completions':loops,'private_pair_hits':pair_hits})
  return
 for s in range(lower,75):search(pool+(s,),s)

search(core,0)
counter12=core+(18,18,18,36,36,63)
assert not any(hall(counter12,t)for t in sources)
assert all(loop(counter12,j)for j in (0,15))
record={'status':'exhaustive in the independently reconstructed directed-corner model',
 'core':core,'total':13,'nodes_by_size':nodes,'soluble_prefixes':pruned,
 'failing_thirteen_source_extensions':failures,'two_own_completion_failures':0,
 'sharp_twelve_source_counterexample':counter12,
 'seconds':time.monotonic()-started,
 'scope':'Computational verification of the nested core. The general reduction requires the written normalization and repeat-restoration argument. No elementary proof of the nested bound or Lean formalisation is claimed.'}
Path('research/elementary-organising/two-loops-independent.json').write_text(json.dumps(record,indent=2)+'\n')
print('Exhausted nested core: nodes',nodes[6:],'failing 13-source extensions',len(failures),'two-loop failures 0.')
print('The 12-source two-loop counterexample fails all 75 targets, checked by Hall.')
print('Seconds',record['seconds'])
