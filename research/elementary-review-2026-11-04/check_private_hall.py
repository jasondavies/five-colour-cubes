from pathlib import Path
exec(Path(__file__).with_name('check_closures.py').read_text().split('# All repeat multisets')[0])
from pathlib import Path
import subprocess
names=['02','12','123','124','023','024','012','234','23','24','34']
cs=[cut(frozenset(map(int,s))) for s in names]
A=cut(frozenset((0,1)))
def target(left,right):return frozenset(('t',a,b) for l,r in ((left,right),(right,left)) for a in l for b in r)
def fromedges(edges):return frozenset(('t',a,b) for e in edges for a,b in (e,e[::-1]))
high=fromedges(['03','04','13','14'])
# Convert string labels to integer tuples.
def opposite(edges):return frozenset(('t',int(a),int(b)) for e in edges for a,b in (e,e[::-1]))
Os=[opposite(['03','04','13','14']),opposite(['01','04','13','34']),opposite(['13','14','23','24'])]
Ts=[target([0,1],[2,3]),target([0,1],[2,4])]
cons=[]
for o in Os:
 for t in Ts:
  corners=list(t); dd={}
  for v in range(1,256):
   D={corners[i] for i in range(8) if v>>i&1}
   rhs=len(D)-3*bool(A&D)-bool(o&D)
   if rhs<=0:continue
   mask=sum((1<<i) for i,c in enumerate(cs) if c&D)
   dd[mask]=max(dd.get(mask,0),rhs)
  cons.append(sorted(dd.items()))
# A loop-free executable check of every small capped outsider count vector.
s='#include <array>\n#include <iostream>\n#include <vector>\n#include <utility>\nusing namespace std;\n'
s+='vector<pair<int,int>> checks[6]={'+','.join('{'+','.join('{'+str(m)+','+str(r)+'}' for m,r in c)+'}' for c in cons)+'};\n'
s+='''array<int,11> g; long long checked=0;
bool hall(int k){for(auto [mask,r]:checks[k]){int n=0;for(int i=0;i<11;i++)if(mask>>i&1)n+=g[i];if(n<r)return false;}return true;}
void test(){
 int p=g[0],q=g[1],l3=g[2],l4=g[3],r3=g[4],r4=g[5],h=g[6],b=g[7],x=g[8],y=g[9],w=g[10];
 int L=b+l3+l4+q+x+y,R=b+p+r3+r4+x+y;
 int a=b+l3+x+w,c=b+l4+y+w,d=b+r4+y+w;
 int v30or31=0,v40or41=0;
'''
for idx,arcs in enumerate([{('t',3,0),('t',3,1)},{('t',4,0),('t',4,1)}]):
 var=['v30or31','v40or41'][idx]
 for i,cc in enumerate(cs):
  if cc&arcs:s+=f'{var}+=g[{i}];\n'
s+='''bool expected[6]={L>=1&&R>=1&&v30or31>=1,L>=1&&R>=1&&v40or41>=1,L>=1&&R>=1&&a>=1&&L+w>=2,L>=1&&R>=1&&d>=1&&R+w>=2,L>=1&&R>=1&&a>=1&&L+w>=2,L>=1&&R>=1&&c>=1&&L+w>=2};
 for(int k=0;k<6;k++)if(hall(k)!=expected[k]){cerr<<"Mismatch "<<k<<":";for(int n:g)cerr<<" "<<n;cerr<<endl;exit(1);}checked++;
}
void enumerate(int i,int left){if(left<0||left>3*(11-i))return;if(i==11){test();return;}for(int n=0;n<=3;n++){g[i]=n;enumerate(i+1,left-n);}}
int main(){enumerate(0,11);cout<<checked<<" capped outsider profiles: all six Hall equivalences pass"<<endl;}
'''
Path('/tmp/check_private_hall.cpp').write_text(s)
subprocess.run(['c++','-std=c++20','-O2','/tmp/check_private_hall.cpp','-o','/tmp/check_private_hall'],check=True)
subprocess.run(['/tmp/check_private_hall'],check=True)
