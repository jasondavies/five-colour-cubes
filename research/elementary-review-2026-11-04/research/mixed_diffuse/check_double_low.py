import sys,json,time,itertools
from pathlib import Path
from check_double_covers import *

def run(total):
 out=[]
 for size in (3,4,5):
  for row in cover_orbits(size):
   js=row['classes'];ops=row['opps'];outside=[j for j in range(35)if (j not in js if j<20 else j+40 not in ops)and j!=20];tested=0;fails=[]
   for ne in range(6-size):
    for ext in itertools.combinations_with_replacement(outside,ne):
     outg=[0]*20;outo=[0]*15
     for j in ext:
      if j<20:outg[j]+=1
      else:outo[j-20]+=1
     if max(outo)>2 or sum(outo)>total-2:continue
     for oo in allocations(total-2-sum(outo),[2]*len(ops)):
      os=outo[:];os[0]=2
      for t,n in zip(ops,oo):os[t-60]+=n
      for gg in allocations(14-total-sum(outg),[3]*len(js)):
       gs=outg[:]
       for j,n in zip(js,gg):gs[j]+=n
       if max(gs)>3:continue
       if any(gs[j]>=3 and sum(gs[k]for k in range(20)if not CUTS[j]&CUTS[k])>1 for j in range(20)):continue
       tested+=1;x=[v for g in gs for v in [g,0,0]]+os
       if solution(x,range(60,75))is None:
        G=conflict_graph(gs,os);fails.append({'g':gs,'o':os,'loops':G['loops'],'edges':G['edges'],'clique':clique_obstruction(gs,G)})
   r={**row,'size':size,'tested':tested,'fails':fails};out.append(r);print(total,size,row['corners'],tested,len(fails),flush=True)
 Path(__file__).with_name(f'double-low-O{total}.json').write_text(json.dumps(out,indent=2))
if __name__=='__main__':run(int(sys.argv[1]))
