"""Discovery of paired small Hall covers; no completeness theorem claimed."""
import sys,json
from pathlib import Path
from itertools import combinations,permutations,product
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'root'))
from cut_model import CUTS,CORNERS,CLASSES,V
P,Q=CORNERS[71],CORNERS[73]
I=P&Q
X,Y=tuple(sorted(P-I)),tuple(sorted(Q-I))
acts=[]
for p in permutations(V):
 for rev in [False,True]:
  def tr(c,p=p,rev=rev):return frozenset(('t',p[b],p[a]) if rev else ('t',p[a],p[b]) for _,a,b in c)
  if {tr(P),tr(Q)}=={P,Q}:acts.append((tr,tuple(CUTS.index(tr(c)) for c in CUTS)))
def allowed(h,t):return tuple(j for j,c in enumerate(CUTS) if c&set(t)<=h)
cx=[(frozenset(h),allowed(frozenset(h),X),3-k) for k in [2,3] for h in combinations(X,k)]
cy=[(frozenset(h),allowed(frozenset(h),Y),3-k) for k in [2,3] for h in combinations(Y,k)]
found={}
for (hx,ax,bx),(hy,ay,by) in product(cx,cy):
 ax,ay=set(ax),set(ay)
 common=ax&ay
 extra=max((bx if ay-ax else 0)+(by if ax-ay else 0),min(bx,by) if len(ax|ay)<20 else 0)
 upper=3*len(common)+extra
 if upper<10:continue
 def key(tr,p):
  a=frozenset(p[j] for j in ax);b=frozenset(p[j] for j in ay)
  return min((tuple(sorted(a)),bx,tuple(sorted(b)),by),(tuple(sorted(b)),by,tuple(sorted(a)),bx))
 canon=min(key(tr,p) for tr,p in acts)
 if canon in found:continue
 found[canon]={'Hx':sorted(hx),'Hy':sorted(hy),'Xclasses':sorted(ax),'Yclasses':sorted(ay),'Xbudget':bx,'Ybudget':by,'common':sorted(common),'maximum_bound':upper}
print('stabilizer actions',len(acts),'paired-cover orbits',len(found))
for r in found.values():print(r)
Path(__file__).with_name('paired-cover-orbits.json').write_text(json.dumps(list(found.values()),indent=2))
