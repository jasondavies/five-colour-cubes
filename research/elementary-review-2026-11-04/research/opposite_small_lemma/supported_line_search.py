from itertools import combinations
import sys
sys.path.insert(0,'research/root');import cut_model as m
for linenum,U in enumerate([m.CORNERS[60]|m.CORNERS[61],m.CORNERS[60]|m.CORNERS[63]]):
 edges=tuple(sorted(U));full=(1<<12)-1
 masks=[sum(1<<i for i,c in enumerate(edges)if c in S) for S in m.CUTS+m.CORNERS[60:]]
 cores=[]
 def rec(i,n,ls,union):
  if not n:
   if union==full:cores.append(tuple(ls))
   return
  for j in range(i,15):
   if ls.count(20+j)<2:rec(j,n-1,ls+[20+j],union|masks[20+j])
 rec(0,5,[],0)
 print('line',linenum,'covered cores',len(cores))
 for Y in range(1<<12):
  k=Y.bit_count()
  if not 3<=k<=9:continue
  ac=[j for j in range(20)if masks[j]&~Y==0]
  if 4*len(ac)<k-1:continue
  outside=set(j for j in range(20,35)if masks[j]&~Y)
  for core in cores:
   out=sum(s in outside for s in core)
   need=k-1+out
   if out<=10-k and need<=4*len(ac):
    gs=[0]*20
    for i in range(9):
     j=next((j for j in ac if gs[j]<4),next(j for j in range(20)if gs[j]<4))
     gs[j]+=1
    print('COUNTER', 'Y', [edges[i]for i in range(12)if Y>>i&1], 'core', [s+40 for s in core], 'gs',gs,'out',out,'ac',ac)
    raise SystemExit
print('none')
