from replacement_geometry import CORNERS,CLASSES,OPP
from itertools import combinations
extras=[18,21,36,39,50,53,56,59]+list(range(60,75))
F={('t',0,2),('t',0,3),('t',1,2),('t',1,3)}
rev={('t',b,a) for _,a,b in F}
for H in [set(),{('t',2,0)},{('t',2,0),('t',3,0)},{('t',2,0),('t',3,1)},rev-{('t',3,1)}]:
 print('COVER',sorted(H),'exception budget',3-len(H))
 for s in extras:
  if CORNERS[s]&rev <=H:
   print(s,CLASSES[s//3] if s<60 else OPP[s-60],sorted(CORNERS[s]&rev))
