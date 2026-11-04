from pathlib import Path
import sys,json
from itertools import combinations,combinations_with_replacement
import networkx as nx
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'elementary-review-2026-11-04/research/root'))
from cut_model import CORNERS,MASKS,KINDS,OPP,solution
core=[0,1,2,45,46,47]
extras=[18,21,36,39,50,53,56,59]+list(range(60,75))
base=[0]*75
for i in core:base[i]+=1
bad=nx.Graph();bad.add_nodes_from(extras);loops=[];targets={}
for a,b in combinations_with_replacement(extras,2):
 x=base.copy();x[a]+=1;x[b]+=1;t=solution(x)
 if t is None:
  if a!=b:bad.add_edge(a,b)
 else:
  targets[f'{a},{b}']=t
  if a==b:loops.append(a)
print('soluble-pair loops',loops)
print('soluble pairs',len(targets),'non-soluble distinct pairs',bad.number_of_edges())
ss=sorted((sorted(c)for c in nx.find_cliques(bad)),key=lambda c:(-len(c),c))
print('maximal pair-compatible supports',len(ss),'sizes',dict(__import__('collections').Counter(map(len,ss))))
for s in ss:print(s)
for a in extras:
 print(a,KINDS[a],'solves with',[b for b in extras if f'{min(a,b)},{max(a,b)}' in targets])
Path('research/elementary-organising/loop-core-pair-graph.json').write_text(json.dumps({'core':core,'extras':extras,'soluble_pair_targets':targets,'maximal_pair_compatible_supports':ss},indent=2)+'\n')
