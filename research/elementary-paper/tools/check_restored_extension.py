#!/usr/bin/env python3
"""Supplementary check of the extension restored during editorial extraction.

This checks all repeat multisets and extra varieties in the directed-corner
model. It is not a premise of the written lemma or an inventory exhaustion
proof of N5=15.
"""
from itertools import combinations, combinations_with_replacement, product

V=frozenset(range(5))
def adjacent(side,repeat):
 side=frozenset(side);poles=side if len(side)==2 else V-side
 assert repeat in V-poles
 return frozenset(('t',a,b) for a in side for b in V-side)|frozenset(('b',repeat,p) for p in poles)
def opposite(left,right):
 return frozenset(('t',a,b) for p,q in ((left,right),(right,left)) for a in p for b in q)
targets=[]
for size in (2,3):
 for side in combinations(range(5),size):
  side=frozenset(side)
  targets.extend(adjacent(side,r) for r in V-(side if size==2 else V-side))
for four in combinations(range(5),4):
 for other in four[1:]:
  left={four[0],other};targets.append(opposite(left,set(four)-left))
assert len(targets)==len(set(targets))==75

def matches(pool,target):
 neighbors=sorted(([i for i,cube in enumerate(pool) if corner in cube] for corner in target),key=len)
 owners=[-1]*len(pool)
 def augment(c,seen):
  for i in neighbors[c]:
   if i in seen:continue
   seen.add(i)
   if owners[i]<0 or augment(owners[i],seen):owners[i]=c;return True
  return False
 return all(augment(c,set()) for c in range(8))

O=opposite({1,2},{3,4})
A=[adjacent({0,1},r) for r in (2,3,4)]
B=[adjacent({1,2,4},r) for r in (1,2,4)]
private_A=frozenset(('t',a,b) for a,b in ((0,2),(0,3),(0,4),(1,2)))
private_B=frozenset(('t',a,b) for a,b in ((1,0),(2,0),(4,0),(4,3)))
extras=[t for t in targets if t!=O]
assert all(t&(private_A|private_B) for t in extras)
checked=0
for aa,bb in product(combinations_with_replacement(range(3),5),repeat=2):
 base=[O]*3+[A[i] for i in aa]+[B[i] for i in bb]
 for Y in extras:
  pool=base+[Y]
  assert any(matches(pool,t) for t in A+B),(aa,bb,Y)
  checked+=1
assert checked==32634
print('Restored extension: all 32,634 repeat/extra-source choices assemble an A or B target.')
print('The 74 nonanchor varieties all meet the union of the two private-corner sets.')
