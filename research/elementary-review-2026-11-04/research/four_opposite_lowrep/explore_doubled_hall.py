from pathlib import Path
import json,sys,collections,itertools
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'root'))
from cut_model import CUTS,CORNERS
data=json.loads(Path(__file__).with_name('bad-classes.json').read_text())
out=[]
for row in data:
 o=row['opposite']
 if len(set(o))==4:continue
 d=next(t for t in o if o.count(t)==2)
 T=sorted(CORNERS[d]);caps=[3 if j in row['bad_classes'] else 1 for j in range(20)]
 cases=[]
 for m in range(1,256):
  S={T[k]for k in range(8)if m>>k&1}
  N=sum(bool(S&CORNERS[t]) for t in o)
  avoid=[j for j,c in enumerate(CUTS)if not S&c]
  cap=sum(caps[j]for j in avoid)
  bound=len(S)-1-N
  if bound>=0 and cap+bound>=10:
   cases.append({'S':['%d%d'%(a,b) for _,a,b in sorted(S)],'O_neighbors':N,'adj_neighbor_bound':bound,'avoiders':avoid,'avoider_cap':cap})
 out.append({'opposite':o,'bad':row['bad_classes'],'cases':cases})
Path(__file__).with_name('doubled-hall-cases.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps([{'opposite':r['opposite'],'ncases':len(r['cases']),'sizes':dict(collections.Counter(len(c['S'])for c in r['cases']))}for r in out],indent=2))
