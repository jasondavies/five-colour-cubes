"""Audit the small tables/assignments in the thirteen-source hand proof.

This checks only its displayed geometric certificates, not inventories.
"""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json

V=set(range(5))
SIDES=[frozenset(s) for n in (2,3) for s in combinations(range(5),n)]
def side(s): return frozenset(map(int,s))
def cut(s):
    s=side(s) if isinstance(s,str) else s
    return {(a,b) for a in s for b in V-s}
def name(s): return ''.join(map(str,sorted(s)))
def target(s):
    a,b=s.split('/')
    return {(x,y) for p,q in ((a,b),(b,a)) for x in map(int,p) for y in map(int,q)}
def corner(s): return tuple(map(int,s))

U=['234','134','123','034']; W=['13','23','24','34']
UP=list(combinations(U,2)); WP=list(combinations(W,2))
T=[
 ['01/24','13/24','01/24','12/34','I','I'],
 ['01/24','13/24','01/24','I','I','12/34'],
 ['01/24','13/24','01/24','12/34','I','I'],
 ['III','02/34','III','12/34','01/24','12/34'],
 ['01/24','03/14','II','12/34','01/24','01/24'],
 ['01/23','12/34','04/12','12/34','01/24','12/34'],
]
assert {name(s) for s in SIDES if not cut(s)&{corner(x) for x in ('03','04','13')}}==set(U+W)
table_count=0
for i,up in enumerate(UP):
 for j,wp in enumerate(WP):
  t=T[i][j]
  if '/' not in t: continue
  core=['01',*up,*wp]; ts=target(t)
  assert ts <= set().union(*(cut(s) for s in core)),(core,t,'unsupported')
  for s in core:
   private=(cut(s)&ts)-set().union(*(cut(v) for v in core if v!=s))
   assert len(private)<=2,(core,t,s,private)
  table_count+=1
assert table_count==27

REPS={'I':{'01','234','02','014','012'},
      'II':{'01','02','124','024','24'},
      'III':{'01','02','124','023','012'}}
MAPS=[
 (0,4,'I',(0,1,2,3,4),True),
 (0,5,'I',(0,1,2,4,3),True),
 (1,3,'I',(0,1,3,4,2),True),
 (1,4,'I',(0,1,4,3,2),True),
 (2,4,'I',(1,0,2,3,4),True),
 (2,5,'I',(1,0,2,4,3),True),
 (3,0,'III',(0,3,1,4,2),True),
 (3,2,'III',(0,3,2,4,1),True),
 (4,2,'II',(1,0,3,2,4),False),
]
for i,j,label,p,rev in MAPS:
 transformed=[]
 for s in ['01',*UP[i],*WP[j]]:
  q={p[v] for v in side(s)}
  transformed.append(name(V-q if rev else q))
 assert set(transformed)==REPS[label],(i,j,transformed)

def avoiding(core,arcs):
 arcs={corner(a) for a in arcs}
 return {name(s) for s in SIDES if name(s) not in core and not cut(s)&arcs}
assert avoiding({'01','02','124','12','012'},['41','42'])=={'03','123','13','023','23','013'}
assert avoiding(REPS['I'],['32','20','40','41'])=={'023'}
assert avoiding(REPS['II'],['02','12','14'])=={'234','023','23','34'}
assert avoiding(REPS['III'],['10','40','43'])=={'03','034','23','013'}

checked=[]
def witness(label,t,assign):
 ts=target(t); chosen=[corner(c) for s,c in assign]
 assert len(chosen)==8 and len(set(chosen))==8 and set(chosen)==ts,(label,chosen,ts)
 counts=Counter(s for s,c in assign)
 for s,c in assign:
  if s.startswith('*'): assert counts[s]==1
  else: assert corner(c) in cut(s) and counts[s]<=2,(label,s,c,counts[s])
 checked.append(label)

witness('F1','03/14',[('*1','31'),('01','04'),('01','13'),('02','01'),('124','40'),('124','43'),('123','10'),('123','34')])
witness('F2-41','01/24',[('*1','41'),('01','02'),('01','12'),('02','04'),('02','21'),('12','20'),('12','14'),('124','40')])
witness('F2-42','02/14',[('*1','42'),('01','04'),('01','12'),('02','01'),('02','21'),('12','10'),('12','24'),('124','40')])
witness('F2-32-34','03/24',[('*1','32'),('*2','34'),('01','02'),('01','04'),('12','20'),('12','23'),('124','40'),('124','43')])
witness('F2-31-34','03/14',[('*1','31'),('*2','34'),('02','01'),('02','04'),('12','10'),('12','13'),('124','40'),('124','43')])
witness('I-32','12/34',[('*1','32'),('01','13'),('01','14'),('234','31'),('234','41'),('02','23'),('02','24'),('014','42')])
for c in ['20','40','41']:
 witness('I-'+c,'01/24',[('*1',c)]+[('234',d) for d in ['20','40','41'] if d!=c]+[('02','04'),('02','21'),('014','02'),('014','12'),('012','14')])
for c in ['02','12','14']:
 witness('II-'+c,'01/24',[('*1',c)]+[('01',d) for d in ['02','12','14'] if d!=c]+[('02','04'),('02','21'),('124','20'),('124','40'),('024','41')])
witness('II-30-31','01/34',[('*1','30'),('*2','31'),('01','04'),('01','14'),('02','03'),('124','13'),('124','40'),('024','41')])
for c in ['10','40','43']:
 witness('III-'+c,'03/14',[('*1',c)]+[('124',d) for d in ['10','40','43'] if d!=c]+[('023','31'),('023','34'),('02','01'),('02','04'),('01','13')])
witness('III-32','03/12',[('*1','32'),('01','02'),('01','13'),('02','01'),('02','23'),('124','10'),('124','20'),('023','31')])

report={'status':'passed','ordinary_table_cells':table_count,'exception_maps':len(MAPS),
        'avoidance_lists':4,'explicit_eight_source_assignments':len(checked),
        'assignments':checked,'scope':'Displayed geometric certificates only; no inventory enumeration.'}
Path('research/elementary_alternative_next/five-repeated-geometry-audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
