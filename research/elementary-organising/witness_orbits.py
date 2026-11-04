from replacement_geometry import *
from itertools import permutations
from collections import Counter
import json
core=[0,1,2,45,46,47]
# Bicolour corners invariant under global reversal.
def transform(c,p,rev):
 if c[0]=='b':return ('b',p[c[1]],p[c[2]])
 return ('t',p[c[2]],p[c[1]])if rev else('t',p[c[1]],p[c[2]])
group=[]
for p in permutations(range(5)):
 for rev in (0,1):
  mp=[CORNERS.index(frozenset(transform(c,p,rev)for c in cs))for cs in CORNERS]
  if sorted(mp[s]for s in core)==core:group.append(mp)
def canonical(x):return min(tuple(sorted(mp[s]for s in x))for mp in group)
data=json.load(open('research/elementary-organising/common-witness-probe.json'))
rows=[tuple(x)for x in data['common_pairs']]+[tuple(r['extras'])for r in data['minimal_no_common_configs']if r['target']is None]
reps=sorted(set(map(canonical,rows)),key=lambda x:(len(x),x))
print('group',len(group),'seedcount',len(rows),'orbits',len(reps),'sizes',Counter(map(len,reps)))
for x in reps:print(x)
