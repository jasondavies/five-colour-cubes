#!/usr/bin/env python3
"""Check the two shortened cap-three Hall criteria, not the full theorem."""
from itertools import product, combinations_with_replacement

V=set(range(5))
sides=[{0,1},{0,2},{1,2,4},{1,2,3},{1,2},{0,1,2}]
cuts=[{(a,b) for a in s for b in V-s} for s in sides]
private=[{(0,2),(1,2)},{(0,1),(2,1)},{(4,0),(4,3)},{(3,0),(3,4)}]

def matches(counts,positions):
 copies=[i for i,n in enumerate(counts) for _ in range(n)]
 ns=sorted(([j for j,i in enumerate(copies) if c in cuts[i]] for c in positions),key=len)
 owners=[-1]*len(copies)
 def augment(k,seen):
  for j in ns[k]:
   if j in seen:continue
   seen.add(j)
   if owners[j]<0 or augment(owners[j],seen):owners[j]=k;return True
  return False
 return all(augment(k,set()) for k in range(len(ns)))

profiles=low=high=0
for counts in product(range(4),repeat=6):
 if sum(counts)!=14:continue
 profiles+=1
 L=counts[0]+counts[1]+counts[5];R=counts[2]+counts[3]+counts[4]
 for a,b in combinations_with_replacement(range(6),2):
  residual=list(counts);residual[a]-=1;residual[b]-=1
  if min(residual)<0:continue
  for t in (4,5):
   assert matches(residual,cuts[t]),(counts,a,b,t)
   low+=1
  for t in range(4):
   if residual[t]<2 or (L if t<2 else R)<6:continue
   rest=residual.copy();rest[t]-=2
   assert matches(rest,cuts[t]-private[t]),(counts,a,b,t)
   high+=1
print(f'{profiles} capped fourteen-source profiles; {low} low-cut and {high} high-cut reservation checks passed.')
print('These checks corroborate the displayed Hall inequalities; they are not a premise of the proof.')
