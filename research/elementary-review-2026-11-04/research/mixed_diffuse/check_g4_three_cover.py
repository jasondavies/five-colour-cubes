import sys,itertools,json,time
from pathlib import Path
sys.path.extend(['research/root','research/mixed_diffuse','research/robust_route'])
from cut_model import *
from check_double_covers import allocations,clique_obstruction
from check_four_adj_four_opp import cases as oldcases
from conflict_graph import conflict_graph

def cases(total):
 hs=[];out=[]
 for c in oldcases():
  h=frozenset(tuple(a)for a in c['H'])
  if h not in hs:hs.append(h)
 for h in hs:
  ops=[o for o in range(60,75)if CORNERS[o]&CUTS[0]<=h];js=[j for j in range(20)if CUTS[j]&CUTS[0]<=h]
  actions=[]
  for p in itertools.permutations(V):
   tr=lambda s:frozenset(('t',p[a],p[b])for _,a,b in s)
   if tr(CUTS[0])==CUTS[0] and tr(h)==h:actions.append([CORNERS.index(tr(c)) for c in CORNERS[60:]])
  osset=set()
  for oo in allocations(total,[2]*len(ops)):
   x=[0]*15
   for o,n in zip(ops,oo):x[o-60]=n
   images=[]
   for p in actions:
    y=[0]*15
    for o,n in enumerate(x):y[p[o]-60]=n
    images.append(tuple(y))
   osset.add(min(images))
  for os in sorted(osset):out.append((h,js,os))
 return out

def main(total):
 results=[]
 for h,js,os in cases(total):
  start=time.monotonic();stats={'tested':0,'oppfail':0,'loopkill':0,'cliquekill':0};fails=[]
  zeros=[i for i,j in enumerate(js)if not CUTS[j]&CUTS[0]]
  for gg in allocations(10-total,[4]*len(js)):
   if sum(gg[i]for i in zeros)>2:continue
   gs=[0]*20;gs[0]=4
   for j,n in zip(js,gg):gs[j]=n
   if any(gs[j]+gs[k]>7 for j in range(20)for k in range(j)if len(CUTS[j]&CUTS[k])==4):continue
   if any(sum(gs[j]for j in range(20)if CLASSES[j][0]==pair)+sum(n for n,(r,p,q)in zip(os,OPP)if pair in (p,q))>7 for pair in PAIRS):continue
   stats['tested']+=1;x=[v for g in gs for v in [g,0,0]]+list(os)
   if solution(x,range(60,75)) is not None:continue
   stats['oppfail']+=1;G=conflict_graph(gs,os)
   if any(gs[j]>3 for j in G['loops']):stats['loopkill']+=1
   elif clique_obstruction(gs,G):stats['cliquekill']+=1
   fails.append({'gs':gs,'loops':G['loops'],'edges':G['edges']})
  r={'H':sorted(h),'js':js,'os':os,**stats,'seconds':time.monotonic()-start,'fails':fails}
  results.append(r);print({k:v for k,v in r.items()if k not in ['fails','js']},flush=True)
 Path(__file__).with_name(f'g4-three-cover-O{total}.json').write_text(json.dumps(results,indent=2))
if __name__=='__main__':main(int(sys.argv[1]))
