from itertools import combinations, combinations_with_replacement, permutations, product
from collections import Counter
V=frozenset(range(5))
sides=[frozenset(s) for n in (2,3) for s in combinations(range(5),n)]
def cut(s):return frozenset(('t',a,b) for a in s for b in V-s)
def adj(s,r):
 p=s if len(s)==2 else V-s
 assert r not in p
 return cut(s)|frozenset(('b',r,a) for a in p)
cuts=[cut(s) for s in sides]
opposites=[]
for four in combinations(range(5),4):
 for q in four[1:]:
  left={four[0],q};right=set(four)-left
  opposites.append(frozenset(('t',a,b) for l,r in ((left,right),(right,left)) for a in l for b in r))
targets=[adj(s,r) for s in sides for r in V-(s if len(s)==2 else V-s)]+opposites
assert len(set(targets))==75

def fits(pool,t):
 ns=[tuple(i for i,s in enumerate(pool) if c in s) for c in t]
 ns.sort(key=len)
 assigned=[-1]*len(pool)
 def augment(c,seen):
  for i in ns[c]:
   if i in seen:continue
   seen.add(i)
   if assigned[i]<0 or augment(assigned[i],seen):
    assigned[i]=c;return True
  return False
 return all(augment(i,set()) for i in range(8))

# All repeat multisets for the nine-source construction, fixing a,b,c,d,e=0,1,2,3,4.
A=frozenset((0,2));B=frozenset((1,2));H=frozenset((0,1,2))
count=0
for o in opposites:
 if ('t',0,1) not in o:continue
 for ra,rb,rh in product(combinations_with_replacement(sorted(V-A),3),combinations_with_replacement(sorted(V-B),3),combinations_with_replacement(sorted(H),2)):
  pool=[o]+[adj(A,r) for r in ra]+[adj(B,r) for r in rb]+[adj(H,r) for r in rh]
  # The hand proof promises an A or B target specifically.
  assert any(fits(pool,adj(s,r)) for s in (A,B) for r in V-s),(o,ra,rb,rh)
  count+=1
print('Nine-source lemma: all',count,'repeat/ opposite choices pass')

# The advertised lower obstruction, with full bicoloured compatibility.
profile=[('01',2,3),('02',1,3),('124',4,3),('123',3,3),('12',0,1),('012',0,1)]
pool=[adj(frozenset(map(int,s)),r) for s,r,n in profile for _ in range(n)]
assert len(pool)==14 and not any(fits(pool,t) for t in targets)
print('Fourteen-source lower obstruction: all 75 targets fail')

# Disjoint-pair replacement and all maximal pairwise-intersecting cut supports.
for i,j in combinations(range(20),2):
 if not cuts[i]&cuts[j]:assert any(o<=cuts[i]|cuts[j] for o in opposites)
adjacency=[{j for j in range(20) if j!=i and cuts[i]&cuts[j]} for i in range(20)]
maximal=[]
def cliques(r,p,x):
 if not p and not x:maximal.append(frozenset(r));return
 pivot=max(p|x,key=lambda v:len(p&adjacency[v]))
 for v in sorted(p-adjacency[pivot]):
  cliques(r|{v},p&adjacency[v],x&adjacency[v]);p.remove(v);x.add(v)
cliques(set(),set(range(20)),set())
base=[['01','02','12','123','124','012'],['01','02','03','04','034','024','023'],['01','02','03','04','034','024','014']]
forms=set()
for row in base:
 for p in permutations(range(5)):
  for rev in (False,True):
   ss=[frozenset(p[int(c)] for c in s) for s in row]
   forms.add(frozenset(sides.index(V-s if rev else s) for s in ss))
assert all(any(s<=f for f in forms) for s in maximal)
print('All',len(maximal),'maximal intersecting supports covered by the three forms')

# Three distinct opposite grid patterns plus one rectangle/full-grid helper.
# An independent augmenting-path matcher for four specified grid positions.
grid=cut(frozenset((0,1)))
rectangles=[target for target in [frozenset(('t',a,b) for a in (0,1) for b in pair) for pair in combinations((2,3,4),2)]]
helpers=[grid,*rectangles]
def rank_patterns(patterns,positions):
 positions=list(positions); owners=[-1]*len(patterns)
 def aug(j,seen):
  for i,p in enumerate(patterns):
   if i in seen or positions[j] not in p:continue
   seen.add(i)
   if owners[i]<0 or aug(owners[i],seen):owners[i]=j;return True
  return False
 return sum(aug(j,set()) for j in range(len(positions)))
checked=exceptions=0
for tri in combinations(opposites,3):
 patterns=[o&grid for o in tri]
 for helper in helpers:
  checked+=1
  if any(rank_patterns(patterns+[helper],r)==4 for r in rectangles):continue
  union=set().union(*patterns)
  assert len(union)==3 and len({b for _,a,b in union})==3
  assert set(patterns)=={frozenset(pair) for pair in combinations(union,2)}
  exceptions+=1
print('Grid lemma:',checked,'pattern/helper checks;',exceptions,'failures all have the stated line form')
