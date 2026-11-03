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
bool hasEdge(const Cube& c,int a,int b) {
 for(auto e:edges) {
  if((c[e[0]]==a&&c[e[1]]==b)||(c[e[0]]==b&&c[e[1]]==a)) return true;
 }
 return false;
}
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
 }
 return false;
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
 }
 return false;
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

 // Weighted geometry for rectangular frames, independently checked by rotations.
 for(int src=0;src<75;++src)for(int target=0;target<75;++target){
  int h=8-std::popcount(cm[src][target]);
  unsigned fitted=edgeMask(varieties[src],varieties[target]);
  std::array<int,3> k{};
  for(int e=0;e<12;++e)if(!(fitted&(1u<<e))){
   int axis=3-edges[e][0]/2-edges[e][1]/2;++k[axis];
  }
  assert(k[0]+k[1]+k[2]<=4);
  for(int i=0;i<3;++i){assert(k[i]<=2);
   for(int j=i+1;j<3;++j){assert(k[i]+k[j]<=3);assert(h+2*(k[i]+k[j])<=12);}
  }
  if(opposite[src])for(auto p:pairs)if(!hasEdge(varieties[src],p[0],p[1])&&!hasEdge(varieties[target],p[0],p[1])){
   int axis=-1;for(int f=0;f<6;++f)if(varieties[target][f]==p[0])axis=f/2;
   assert(axis>=0&&h<=4&&k[axis]<=2);
   for(int j=0;j<3;++j)if(j!=axis)assert(k[j]==0);
  }
 }
 std::cout<<"Rectangular geometry verified: all directional edge bounds, zero-short-edge bounds, and common-missing-pair alignment.\n";

 // All three possible axes of each of the 75 target varieties.
 int oriented=0,eligible=0;int firstChecks=0,secondChecks=0;
 for(int t=0;t<75;++t)for(int axis=0;axis<3;++axis){
  ++oriented;bool axisMono=false,offMono=false;
  for(auto e:edges)if(varieties[t][e[0]]==varieties[t][e[1]]){
   if(3-e[0]/2-e[1]/2==axis)axisMono=true;else offMono=true;
  }
  // axis is the long axis for 2 x 2 x c.
  if(!axisMono){++eligible;
   for(int src=0;src<75;++src){
    unsigned fit=edgeMask(varieties[src],varieties[t]);int h=8-std::popcount(cm[src][t]);int k=0;
    for(int e=0;e<12;++e)if(3-edges[e][0]/2-edges[e][1]/2==axis&&!(fit&(1u<<e)))++k;
    assert(k<=2&&h+k<=8);++firstChecks;
   }
  }
  // axis is the length-two direction for 2 x 3 x c.
  if(!offMono)for(int src=0;src<75;++src){
   unsigned fit=edgeMask(varieties[src],varieties[t]);int h=8-std::popcount(cm[src][t]);std::array<int,3> k{};
   for(int e=0;e<12;++e)if(!(fit&(1u<<e)))++k[3-edges[e][0]/2-edges[e][1]/2];
   int total=k[0]+k[1]+k[2]-k[axis];assert(h+total<=9);
   for(int j=0;j<3;++j)if(j!=axis)assert(k[j]<=2);
   ++secondChecks;
  }
 }
 assert(oriented==225);
 std::cout<<oriented<<" oriented targets: "<<eligible<<" have no monochromatic long edge; "<<firstChecks<<" weighted 2x2xc checks and "<<secondChecks<<" weighted 2x3xc checks passed.\n";

 auto cornerTypes=[](const Cube& c){
  std::set<Corner> out;
  for(int a=0;a<2;++a)for(int b=0;b<2;++b)for(int d=0;d<2;++d){
   Corner x={c[a],c[2+b],c[4+d]};if((a+b+d)%2)std::swap(x[1],x[2]);
   out.insert(std::min({x,Corner{x[1],x[2],x[0]},Corner{x[2],x[0],x[1]}}));
  }
  return out;
 };
 std::array<std::set<Corner>,75> keys;
 for(int i=0;i<75;++i)keys[i]=cornerTypes(varieties[i]);
 std::set<std::pair<int,int>> outsideExpected={{4,0},{2,1},{1,2},{2,2},{0,4}};
 std::set<Corner> positive01,negative01;
 for(auto pair:pairs){
  int first=-1;std::vector<int> family;
  for(int i=0;i<75;++i)if(!hasEdge(varieties[i],pair[0],pair[1])){family.push_back(i);if(!opposite[i]&&first<0)first=i;}
  assert(first>=0&&family.size()==9);std::set<Corner> positive,negative;
  for(auto x:keys[first])if(x[0]!=x[1]&&x[0]!=x[2]&&x[1]!=x[2]){
   positive.insert(x);Corner y={x[0],x[2],x[1]};negative.insert(std::min({y,Corner{y[1],y[2],y[0]},Corner{y[2],y[0],y[1]}}));
  }
  assert(positive.size()==6&&negative.size()==6);
  std::set<std::pair<int,int>> outside,inside;
  for(int w=0;w<75;++w){int pos=0,neg=0;for(auto x:keys[w]){pos+=positive.count(x);neg+=negative.count(x);}
   bool fam=std::find(family.begin(),family.end(),w)!=family.end();(fam?inside:outside).insert({pos,neg});
   assert(pos>0||neg>=4);assert(pos>1||neg>=2);assert(pos>2||neg>=1);
  }
  assert(outside==outsideExpected);
  assert((inside==std::set<std::pair<int,int>>{{6,0},{0,6},{4,4}}));
  if(pair==Edge{0,1}){positive01=positive;negative01=negative;}
 }
 std::cout<<"All ten signed projections agree with the claimed profiles and the 4/2/1 lower bounds.\n";
 // Check each stated normal-form corner disjunction for all adjacent-repeat sources.
 for(int w=0;w<75;++w)if(!opposite[w]){
  if(!hasEdge(varieties[w],0,3))assert((cyclicCorner(varieties[w],{0,2,4})&&cyclicCorner(varieties[w],{0,4,1}))||cyclicCorner(varieties[w],{1,2,3}));
  if(!hasEdge(varieties[w],1,3))assert(cyclicCorner(varieties[w],{0,3,2})||(cyclicCorner(varieties[w],{0,4,1})&&cyclicCorner(varieties[w],{1,4,2})));
  if(!hasEdge(varieties[w],1,4))assert((cyclicCorner(varieties[w],{0,1,3})&&cyclicCorner(varieties[w],{1,2,3}))||cyclicCorner(varieties[w],{0,2,4}));
 }
 std::cout<<"All three transverse-edge orientation disjunctions verified.\n";
 // Geometric normal forms: swap poles, permute ring colours, optionally reflect.
 for(bool mirror:{false,true}){
  std::set<int> remaining;for(int w=0;w<75;++w)if(hasEdge(varieties[w],0,1))remaining.insert(w);
  int orbits=0;
  while(!remaining.empty()){
   int rep=*remaining.begin();std::set<int> orbit;
   std::array<int,3> ring={2,3,4};do{for(int swap=0;swap<2;++swap)for(int reflection=0;reflection<=int(mirror);++reflection){
    Cube c=varieties[rep];if(reflection)std::swap(c[0],c[1]);
    std::array<int,5> map={swap,1-swap,ring[0],ring[1],ring[2]};for(auto& v:c)v=map[v];c=canonical(c);
    int id=int(std::lower_bound(varieties.begin(),varieties.end(),c)-varieties.begin());assert(id<75&&varieties[id]==c);orbit.insert(id);
   }}while(std::next_permutation(ring.begin(),ring.end()));
   for(int w:orbit){remaining.erase(w);}++orbits;
   if(mirror){std::cout<<"Normal form ";for(int a:varieties[rep])std::cout<<a;std::cout<<", orbit size "<<orbit.size()<<", signed profiles ";std::set<std::pair<int,int>> profiles;
    for(int w:orbit){int pos=0,neg=0;for(auto x:keys[w]){pos+=positive01.count(x);neg+=negative01.count(x);}profiles.insert({pos,neg});}
    for(auto [pos,neg]:profiles){std::cout<<'('<<pos<<','<<neg<<") ";}std::cout<<'\n';
   }
  }
  std::cout<<"Outside-family orbits "<<(mirror?"with reflection":"without reflection")<<": "<<orbits<<'\n';
 }
 // Uniform three-variety obstruction, with coefficients valid for every length.
 const Cube rawA={0,1,0,2,3,4},rawB={0,1,1,2,3,4},rawC={0,3,1,4,2,3};
 auto index=[&](Cube c){c=canonical(c);auto it=std::lower_bound(varieties.begin(),varieties.end(),c);assert(it!=varieties.end()&&*it==c);return int(it-varieties.begin());};
 int A=index(rawA),B=index(rawB),C=index(rawC);
 std::set<int> supported;
 for(int t=0;t<75;++t)if((cm[A][t]|cm[B][t]|cm[C][t])==255)supported.insert(t);
 assert((supported==std::set<int>{A,B,C}));
 assert(std::popcount(cm[B][A]|cm[C][A])==6);
 assert(std::popcount(cm[C][B])==1);
 assert(std::popcount(cm[A][C]|cm[B][C])==1);
 auto edgeDefect=[&](unsigned fitted,int axis){int k=0;for(int e=0;e<12;++e)if(3-edges[e][0]/2-edges[e][1]/2==axis&&!(fitted&(1u<<e)))++k;return k;};
 for(int axis=0;axis<3;++axis){
  assert(edgeDefect(edgeMask(varieties[C],varieties[B]),axis)==1);
  assert(edgeDefect(edgeMask(varieties[A],varieties[C])|edgeMask(varieties[B],varieties[C]),axis)==1);
 }
 std::cout<<"Uniform obstruction verified: only A,B,C targets; private demands 2, S+7, S+7.\n";
 int rodChecks=0,stripChecks=0;
 for(int t=0;t<75;++t)for(int longAxis=0;longAxis<3;++longAxis){
  bool transverse=true,axial=varieties[t][2*longAxis]==varieties[t][2*longAxis+1];
  unsigned longMask=0;
  for(int e=0;e<12;++e)if(3-edges[e][0]/2-edges[e][1]/2==longAxis){longMask|=1u<<e;if(varieties[t][edges[e][0]]==varieties[t][edges[e][1]])transverse=false;}
  std::vector<unsigned> candidates;
  if((!opposite[t]&&transverse)||(opposite[t]&&axial)){
   for(int s=0;s<75;++s){int h=8-std::popcount(cm[s][t]);unsigned miss=(~edgeMask(varieties[s],varieties[t]))&longMask;int k=std::popcount(miss);
    if(!opposite[t]){
     if(!opposite[s]){assert(k<=1&&h+2*k<=9);}else{assert(k<=2&&h<=6);if(k==2)candidates.push_back(miss);}
    }else{
     assert(k<=2&&h+2*k<=8);
     if(h+3*k==10){assert(opposite[s]&&repeated[s]==repeated[t]&&s!=t&&k==2&&h==4);candidates.push_back(miss);}
     else assert(h+3*k<10);
    }
    ++rodChecks;
   }
   assert(candidates.size()==2);assert((candidates[0]&candidates[1])==0);
  }
  for(int shortAxis=0;shortAxis<3;++shortAxis)if(shortAxis!=longAxis){
   int unitAxis=3-shortAxis-longAxis;bool offMono=false;
   for(int e=0;e<12;++e)if(3-edges[e][0]/2-edges[e][1]/2!=shortAxis&&varieties[t][edges[e][0]]==varieties[t][edges[e][1]])offMono=true;
   if(offMono)continue;
   unsigned activeMask=0;for(int e=0;e<12;++e)if(3-edges[e][0]/2-edges[e][1]/2!=shortAxis)activeMask|=1u<<e;
   std::set<unsigned> equalitySignatures;
   for(int s=0;s<75;++s){int h=8-std::popcount(cm[s][t]);unsigned fitted=edgeMask(varieties[s],varieties[t]);int k=edgeDefect(fitted,longAxis),j=edgeDefect(fitted,unitAxis);
    assert(k<=2);
    if(!opposite[s])assert(h+j+2*k<=10);else assert(h+j+2*k<=11);
    if(h+j+2*k==11){assert(opposite[s]&&h==6&&k==2&&j==1);unsigned sig=((255^cm[s][t])<<12)|((~fitted)&activeMask);assert(equalitySignatures.insert(sig).second);}
    if(opposite[t]&&varieties[t][2*shortAxis]==varieties[t][2*shortAxis+1])assert(h+j+2*k<=10);
    ++stripChecks;
   }
  }
 }
 std::cout<<rodChecks<<" rod profiles and "<<stripChecks<<" strip profiles verify the affine bounds and concentration equality cases.\n";
}
