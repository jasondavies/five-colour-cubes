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
 for(auto s:varieties){std::vector<Edge> missing;for(auto p:pairs)if(!hasEdge(s,p[0],p[1]))missing.push_back(p);
  assert(missing.size()==(opp(s)?2u:1u));
  if(missing.size()==2)for(int a:missing[0])for(int b:missing[1])assert(a!=b);
 }
 int uniquePairs=0;
 for(size_t i=0;i<pairs.size();++i)for(size_t j=i+1;j<pairs.size();++j){int count=0;for(auto s:varieties)if(!hasEdge(s,pairs[i][0],pairs[i][1])&&!hasEdge(s,pairs[j][0],pairs[j][1])){++count;assert(opp(s));}
  bool disjoint=true;for(int a:pairs[i])for(int b:pairs[j])disjoint&=a!=b;
  assert(count==(disjoint?1:0));uniquePairs+=count;
 }
 std::array<std::array<int,4>,4> minima;for(auto& row:minima)row.fill(100);
 std::map<std::pair<int,int>,int> profiles;
 int checks=0;
 for(auto t:varieties)for(auto s:varieties){int c=std::popcount(cornerMask(s,t)),e=std::popcount(edgeMask(s,t));int row=2*opp(t)+opp(s);
  minima[row][0]=std::min(minima[row][0],c);minima[row][1]=std::min(minima[row][1],e);minima[row][2]=std::min(minima[row][2],c+e);
  assert(e>=8&&c+e>=10);if(opp(t))assert(e>=9&&c+e>=11);if(opp(s)||opp(t))assert(c>=2);
  if(!opp(t)&&!opp(s)&&e==9)assert(c>=1);
  // These two inequalities imply c+q*e >= 8q+2 for every q>=1;
  // with an opposite-repeat target they imply >= 9q+2.
  ++profiles[{c,e}];++checks;
 }
 int orientationChecks=0;
 for(auto s:varieties)if(!opp(s)&&!hasEdge(s,0,3)){
  assert(cyclicCorner(s,{1,2,3}) || (cyclicCorner(s,{0,2,4})&&cyclicCorner(s,{0,4,1})));
  ++orientationChecks;
 }
 std::cout<<"24 rotations from quarter-turn generators, 75 varieties; "<<checks<<" direct rotation compatibility pairs checked.\n";
 for(int row=0;row<4;++row)std::cout<<"target "<<(row/2?"opposite":"adjacent")<<", source "<<(row%2?"opposite":"adjacent")<<": min corners "<<minima[row][0]<<", min edges "<<minima[row][1]<<", min sum "<<minima[row][2]<<"\n";
 std::cout<<uniquePairs<<" disjoint missing-pair pairs have a unique opposite-repeat variety; intersecting pairs have none.\n";
 std::cout<<orientationChecks<<" normalised adjacent sources pass the stated cyclic-corner disjunction.\n";
 std::cout<<"General-q compatibility bounds follow from the checked edge and total minima.\n";
}
