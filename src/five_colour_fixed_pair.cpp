// Independent direct-rotation audit of the rare-pair frame geometry.
#ifdef NDEBUG
#error "This verification program requires assertions enabled"
#endif
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <iostream>
#include <map>
#include <set>
#include <vector>
using Cube=std::array<int,6>;
using Edge=std::array<int,2>;
using Corner=std::array<int,3>;
std::vector<Cube> rotations, varieties;
std::vector<Edge> edges;
std::vector<Corner> corners;
Cube canonical(Cube c) {
  Cube out=c;
  for(auto r:rotations) {Cube d;for(int f=0;f<6;++f)d[f]=c[r[f]];out=std::min(out,d);}
  return out;
}
bool opp(const Cube& c){return c[0]==c[1]||c[2]==c[3]||c[4]==c[5];}
bool hasEdge(const Cube& c,int a,int b){for(auto e:edges)if((c[e[0]]==a&&c[e[1]]==b)||(c[e[0]]==b&&c[e[1]]==a))return true;return false;}
unsigned cornerMask(const Cube& s,const Cube& t){
 unsigned m=0;for(unsigned k=0;k<corners.size();++k)for(auto r:rotations){bool ok=true;for(int f:corners[k])ok&=s[r[f]]==t[f];if(ok)m|=1u<<k;}return m;
}
unsigned edgeMask(const Cube& s,const Cube& t){
 unsigned m=0;for(unsigned k=0;k<edges.size();++k)for(auto r:rotations){bool ok=true;for(int f:edges[k])ok&=s[r[f]]==t[f];if(ok)m|=1u<<k;}return m;
}
bool cyclicCorner(const Cube& c,Corner desired){
 for(int a=0;a<2;++a)for(int b=0;b<2;++b)for(int d=0;d<2;++d){
  Corner x={c[a],c[2+b],c[4+d]};if((a+b+d)%2)std::swap(x[1],x[2]);
  for(int k=0;k<3;++k)if(x[k]==desired[0]&&x[(k+1)%3]==desired[1]&&x[(k+2)%3]==desired[2])return true;
 }return false;
}

std::array<std::array<unsigned,75>,75> cm;
std::array<int,75> repeated;
std::array<bool,75> opposite;
unsigned coreMask(int s,int t) {
 unsigned m=cm[s][t];
 if(!opposite[t] && hasEdge(varieties[s],repeated[t],repeated[t]))m|=256;
 return m;
}
bool augment(int pos,const std::array<unsigned,12>& masks,int count,
             std::array<int,12>& owner,unsigned& visited) {
 for(int j=0;j<count;++j)if(!(visited&(1u<<j))&&(masks[j]&(1u<<pos))) {
  visited|=1u<<j;
  if(owner[j]<0||augment(owner[j],masks,count,owner,visited)){owner[j]=pos;return true;}
 }return false;
}
bool matches(int t,const std::array<int,9>& ids,const std::array<int,9>& x,bool core,int extra=-1){
 std::array<unsigned,12> masks{};int count=0;
 for(int i=0;i<9;++i)for(int j=0;j<x[i];++j)masks[count++]=core?coreMask(ids[i],t):cm[ids[i]][t];
 if(extra>=0)masks[count++]=core?coreMask(extra,t):cm[extra][t];
 std::array<int,12> owner;owner.fill(-1);
 int slots=core&&!opposite[t]?9:8;
 for(int p=0;p<slots;++p){unsigned visited=0;if(!augment(p,masks,count,owner,visited))return false;}
 return true;
}
int main(){
 const Cube id={0,1,2,3,4,5},rx={0,1,4,5,3,2},ry={5,4,2,3,0,1};
 std::set<Cube> group{id};std::vector<Cube> todo{id};
 for(size_t i=0;i<todo.size();++i)for(auto r:{rx,ry}){Cube p;for(int f=0;f<6;++f)p[f]=todo[i][r[f]];if(group.insert(p).second)todo.push_back(p);}
 rotations.assign(group.begin(),group.end());assert(rotations.size()==24);
 std::set<Cube> types;
 for(int code=0;code<15625;++code){int v=code,mask=0;Cube c;for(auto& a:c){a=v%5;v/=5;mask|=1<<a;}if(mask==31)types.insert(canonical(c));}
 varieties.assign(types.begin(),types.end());assert(varieties.size()==75);
 for(int a=0;a<6;++a)for(int b=a+1;b<6;++b)if(a/2!=b/2)edges.push_back({a,b});
 for(int a=0;a<2;++a)for(int b=2;b<4;++b)for(int c=4;c<6;++c)corners.push_back({a,b,c});
 std::vector<Edge> pairs;for(int a=0;a<5;++a)for(int b=a+1;b<5;++b)pairs.push_back({a,b});

 for(int s=0;s<75;++s){
  opposite[s]=opp(varieties[s]);
  for(int a=0;a<5;++a)if(std::count(varieties[s].begin(),varieties[s].end(),a)==2)repeated[s]=a;
  std::set<Corner> types;
  for(int a=0;a<2;++a)for(int b=0;b<2;++b)for(int d=0;d<2;++d){
   Corner x={varieties[s][a],varieties[s][2+b],varieties[s][4+d]};if((a+b+d)%2)std::swap(x[1],x[2]);
   types.insert(std::min({x,Corner{x[1],x[2],x[0]},Corner{x[2],x[0],x[1]}}));
  }assert(types.size()==8);
  for(int t=0;t<75;++t){cm[s][t]=cornerMask(varieties[s],varieties[t]);
   int c=std::popcount(cm[s][t]),e=std::popcount(edgeMask(varieties[s],varieties[t]));
   assert(c+e>=10&&e>=8);if(opp(varieties[t]))assert(c+e>=11&&e>=9);
  }
 }
 std::array<int,9> fixed{};int familyChecks=0;
 for(auto pair:pairs){
  std::vector<int> ids,os,as,plus,minus;
  for(int s=0;s<75;++s)if(!hasEdge(varieties[s],pair[0],pair[1])){ids.push_back(s);(opposite[s]?os:as).push_back(s);}
  assert(ids.size()==9&&os.size()==3&&as.size()==6);
  for(int s:as)(std::popcount(cm[s][as[0]])>=6?plus:minus).push_back(s);
  assert(plus.size()==3&&minus.size()==3);
  std::set<int> pr,mr;for(int s:plus)pr.insert(repeated[s]);for(int s:minus)mr.insert(repeated[s]);assert(pr.size()==3&&pr==mr);
  for(int t:os){unsigned pc=cm[plus[0]][t],mc=cm[minus[0]][t];assert(std::popcount(pc)==4&&std::popcount(mc)==4&&(pc|mc)==255&&(pc&mc)==0);
   for(int s:plus){assert(cm[s][t]==pc);}
   for(int s:minus){assert(cm[s][t]==mc);}
   unsigned rowUnion=0;
   for(int s:os)if(s!=t){unsigned row=cm[s][t];assert(std::popcount(row)==4&&std::popcount(row&pc)==2&&std::popcount(row&mc)==2);assert(!(rowUnion&row));rowUnion|=row;}
   assert(rowUnion==255);for(int s:ids)assert(std::popcount(cm[s][t])>=4&&std::popcount(cm[t][s])>=4);
   ++familyChecks;
  }
  for(int t:as){unsigned tri=0;
   for(int k=0;k<8;++k){auto f=corners[k];int a=varieties[t][f[0]],b=varieties[t][f[1]],c=varieties[t][f[2]];if(a!=b&&a!=c&&b!=c)tri|=1u<<k;}
   assert(std::popcount(tri)==6);
   for(int s:ids){unsigned special=(cm[s][t]&~tri)|((coreMask(s,t))&256);
    assert(std::popcount(special)==(!opposite[s]&&repeated[s]==repeated[t]?3:0));
    if(!opposite[s]){
     bool same=(std::find(plus.begin(),plus.end(),s)!=plus.end())==(std::find(plus.begin(),plus.end(),t)!=plus.end());
     assert((cm[s][t]&tri)==(same?tri:0));
    }
   }
   ++familyChecks;
  }
  if(pair==Edge{0,1})std::copy(ids.begin(),ids.end(),fixed.begin());
 }
 std::vector<std::array<int,9>> failures;std::array<int,9> x{};long long inventories=0,hasOpposite=0;
 auto enumerate=[&](auto&& self,int i,int remaining)->void {
  if(i<8){for(int c=0;c<=remaining;++c){x[i]=c;self(self,i+1,remaining-c);}return;}
  x[8]=remaining;++inventories;bool corner=false,core=false,op=false;
  for(int j=0;j<9;++j){op|=opposite[fixed[j]]&&x[j]>0;corner|=matches(fixed[j],fixed,x,false);core|=matches(fixed[j],fixed,x,true);}
  assert(corner);if(op){++hasOpposite;assert(core);}if(!core)failures.push_back(x);
 };
 enumerate(enumerate,0,11);assert(inventories==75582&&failures.size()==24);
 int extensions=0;for(const auto& y:failures)for(int w=0;w<75;++w){bool ok=false;for(int t:fixed)ok|=matches(t,fixed,y,true,w);assert(ok);++extensions;}
 assert(extensions==1800);
 std::cout<<"24 proper rotations; 75 varieties; 5,625 direct source-target checks; eight distinct corner types per variety.\n";
 std::cout<<"10 missing-pair families; "<<familyChecks<<" target incidence patterns verified, including all four cells and common tricoloured corners.\n";
 std::cout<<inventories<<" eleven-cube multiplicity vectors: all admit a family corner solution; "<<hasOpposite<<" contain an opposite-repeat copy, all admit a core matching.\n";
 std::cout<<failures.size()<<" core-matching failures without the extra cube; "<<extensions<<" arbitrary one-cube extensions all succeed.\n";
}
