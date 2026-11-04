from replacement_geometry import CORNERS,CLASSES,OPP
from itertools import combinations
core=[0,1,2,45,46,47]
extras=[18,21,36,39,50,53,56,59]+list(range(60,75))
clauses={}
for t,cs in enumerate(CORNERS):
 cs=sorted(cs);raw={}
 for mask in range(1,256):
  D={cs[i] for i in range(8) if mask>>i&1}
  cap=len(D)-1-sum(bool(D&CORNERS[s]) for s in core)
  if cap<0:continue
  ns=sum(1<<i for i,s in enumerate(extras) if D&CORNERS[s])
  if ns not in raw or cap>raw[ns][0]:raw[ns]=(cap,sorted(D))
 # retain weakest inequalities: deficiency is disjunction
 kept={ns:(c,D) for ns,(c,D) in raw.items() if not any(ns2!=ns and ns2&~ns==0 and c2>=c for ns2,(c2,D2)in raw.items())}
 if 0 in kept:continue
 clauses[t]=kept
for t,kept in clauses.items():
 print('TARGET',t,CLASSES[t//3]if t<60 else OPP[t-60],'clauses',len(kept))
 for ns,(cap,D) in kept.items():print(' ',[extras[i]for i in range(23)if ns>>i&1],'<=' ,cap,'D',D)
