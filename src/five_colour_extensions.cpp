// Independent geometry and small-support checks for Sections 6–7.
// Regenerates varieties from face colourings; reads no generated Lean data.
#ifdef NDEBUG
#error "This verification program requires assertions enabled"
#endif
#include <algorithm>
#include <array>
#include <bit>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <map>
#include <numeric>
#include <set>
#include <string>
#include <vector>
#include <omp.h>
using Cube=std::array<int,6>;
using Triple=std::array<int,3>;
std::vector<Cube> rotations, cubes;
std::array<std::array<int,8>,75> corners;
std::array<std::array<int,25>,75> edges;
std::array<std::array<unsigned,75>,75> fits;
std::array<std::array<bool,125>,75> hasCorner{};
Cube canonical(Cube c) {
  Cube best=c;
  for(auto r:rotations) { Cube d; for(int f=0;f<6;++f)d[f]=c[r[f]]; best=std::min(best,d); }
  return best;
}
int index(Cube c) { c=canonical(c);auto p=std::lower_bound(cubes.begin(),cubes.end(),c);assert(p!=cubes.end()&&*p==c);return int(p-cubes.begin()); }
int repeated(int i) {std::array<int,5> n{};for(int a:cubes[i])if(++n[a]==2)return a;std::abort();}
bool opposite(int i) {for(int a=0;a<3;++a)if(cubes[i][2*a]==cubes[i][2*a+1])return true;return false;}
int pairKey(int a,int b) {return 5*std::min(a,b)+std::max(a,b);}
struct Demand {std::array<int,8> need{};};
// Hall grouped by available source varieties: for every subset J of the
// sources, slots whose available sources lie entirely in J need <= supply(J).
Demand demand(int t,const std::array<int,3>& src,int k,int q) {
  Demand d;
  for(int p=0;p<8;++p) {
    int m=0;for(int j=0;j<k;++j)if(fits[t][src[j]]&(1u<<p))m|=1<<j;
    ++d.need[m];
  }
  if(q)for(int e=0;e<25;++e)if(edges[t][e]) {
    int m=0;for(int j=0;j<k;++j)if(edges[src[j]][e])m|=1<<j;
    d.need[m]+=q*edges[t][e];
  }
  for(int j=0;j<k;++j)for(int m=0;m<(1<<k);++m)if(m&(1<<j))d.need[m]+=d.need[m^(1<<j)];
  return d;
}
bool feasible(const Demand& d,const std::array<int,3>& counts,int k) {
  for(int m=0;m<(1<<k);++m) {
    int cap=0;for(int j=0;j<k;++j)if(m&(1<<j))cap+=counts[j];
    if(d.need[m]>cap)return false;
  }
  return true;
}
bool solve(const std::array<int,3>& src,const std::array<int,3>& counts,int k,int q=0) {
  for(int t=0;t<75;++t)if(feasible(demand(t,src,k,q),counts,k))return true;
  return false;
}
std::set<int> compatible(const std::vector<int>& src) {
  std::set<int> out;
  for(int t=0;t<75;++t) {unsigned m=0;for(int s:src)m|=fits[t][s];if(m==255)out.insert(t);}
  return out;
}
int privateCount(int t,const std::vector<int>& others) {
  unsigned m=0;for(int s:others)m|=fits[t][s];return 8-std::popcount(m);
}
int main(int argc, char** argv) {
  bool triples = argc == 2 && std::string(argv[1]) == "--three-variety-frame";
  if (argc != 1 && !triples) {
    std::cerr << "usage: " << argv[0] << " [--three-variety-frame]\n";
    return 2;
  }
  std::array<int,3> p={0,1,2};
  do {int inv=0;for(int a=0;a<3;++a)for(int b=a+1;b<3;++b)inv+=p[a]>p[b];
    for(int signs=0;signs<8;++signs)if((std::popcount(unsigned(signs))+inv)%2==0) {
      Cube r;for(int f=0;f<6;++f)r[f]=2*p[f/2]+((f%2)^((signs>>(f/2))&1));rotations.push_back(r);
    }
  }while(std::next_permutation(p.begin(),p.end()));
  assert(rotations.size()==24);
  std::set<Cube> all;
  for(int code=0;code<15625;++code) {Cube c;int v=code,mask=0;for(int& a:c){a=v%5;v/=5;mask|=1<<a;}if(mask==31)all.insert(canonical(c));}
  cubes.assign(all.begin(),all.end());assert(cubes.size()==75);
  for(int i=0;i<75;++i) {
    for(int k=0;k<8;++k) {
      Triple c={cubes[i][(k>>2)&1],cubes[i][2+((k>>1)&1)],cubes[i][4+(k&1)]};
      if(std::popcount(unsigned(k))%2)std::swap(c[1],c[2]);
      int key=125;for(int j=0;j<3;++j)key=std::min(key,25*c[j]+5*c[(j+1)%3]+c[(j+2)%3]);
      corners[i][k]=key;hasCorner[i][key]=true;
    }
    for(int f=0;f<6;++f)for(int g=f+1;g<6;++g)if(f/2!=g/2)++edges[i][pairKey(cubes[i][f],cubes[i][g])];
  }
  for(int t=0;t<75;++t)for(int s=0;s<75;++s)for(int k=0;k<8;++k)if(hasCorner[s][corners[t][k]])fits[t][s]|=1u<<k;
  int minSingle=12,minPair=12;
  for(int t=0;t<75;++t) {
    int r=repeated(t),mono=0;assert(0<=r&&r<5);
    for(int a=0;a<5;++a)for(int b=a;b<5;++b){int n=edges[t][pairKey(a,b)];if(a==b){mono+=n;assert(!n||a==r);}else{assert(n<=2);assert(n!=2||a==r||b==r);}}
    assert(mono<=1);
    for(int a=0;a<5;++a)if(a!=r)assert(edges[t][pairKey(a,r)]);
    for(int a=0;a<75;++a){int n=0;for(int e=0;e<25;++e)if(edges[a][e])n+=edges[t][e];minSingle=std::min(minSingle,n);
      for(int b=a+1;b<75;++b){int both=0;for(int e=0;e<25;++e)if(edges[a][e]||edges[b][e])both+=edges[t][e];minPair=std::min(minPair,both);}}
  }
  std::cout<<"75 varieties, reserve geometry checked; minimum edge coverage: one source "<<minSingle<<", two distinct "<<minPair<<std::endl;
  assert(minSingle==8&&minPair==9);
  int disjoint=0;std::set<int> orbits;
  for(int a=0;a<75;++a)for(int b=a+1;b<75;++b) {
    for(int c=1;c<13;++c)assert(solve({a,b,0},{c,13-c,0},2));
    bool shared=false;for(int key=0;key<125;++key)shared|=hasCorner[a][key]&&hasCorner[b][key];
    if(shared)continue;
    ++disjoint;bool found=false;
    for(int t=0;t<75;++t)if(opposite(t)&&std::popcount(fits[t][a])==4&&std::popcount(fits[t][b])==4&&(fits[t][a]|fits[t][b])==255)found=true;
    assert(found);
    std::array<int,5> perm={0,1,2,3,4};int rep=75*75;
    do {Cube ca=cubes[a],cb=cubes[b];for(int& c:ca)c=perm[c];for(int& c:cb)c=perm[c];int ia=index(ca),ib=index(cb);if(ia>ib)std::swap(ia,ib);rep=std::min(rep,75*ia+ib);}while(std::next_permutation(perm.begin(),perm.end()));
    orbits.insert(rep);
  }
  assert(disjoint==330&&orbits.size()==5);
  std::cout<<"All two-variety size-13 collections solve; "<<disjoint<<" disjoint pairs, "<<orbits.size()<<" colour orbits, all have 4+4 opposite-repeat targets"<<std::endl;
  std::array<std::pair<Cube,Cube>,5> witnesses={{{{0,1,0,2,3,4},{0,1,1,2,4,3}},{{0,1,0,2,3,4},{0,1,2,3,2,4}},{{0,1,0,2,3,4},{0,1,2,3,3,4}},{{0,1,0,2,3,4},{0,1,2,4,3,4}},{{0,1,0,2,3,4},{0,3,0,4,1,2}}}};
  std::set<int> witnessOrbits;
  for(int i=0;i<5;++i){int a=index(witnesses[i].first),b=index(witnesses[i].second),t=index(i==0||i==4?Cube{0,0,1,2,3,4}:Cube{0,1,2,2,3,4});assert(std::popcount(fits[t][a])==4&&std::popcount(fits[t][b])==4&&(fits[t][a]|fits[t][b])==255);
    std::array<int,5> perm={0,1,2,3,4};int rep=75*75;
    do{Cube ca=cubes[a],cb=cubes[b];for(int& c:ca)c=perm[c];for(int& c:cb)c=perm[c];int ia=index(ca),ib=index(cb);if(ia>ib)std::swap(ia,ib);rep=std::min(rep,75*ia+ib);}while(std::next_permutation(perm.begin(),perm.end()));
    witnessOrbits.insert(rep);
  }
  assert(witnessOrbits==orbits);
  int P=index({0,1,0,2,3,4}),Q=index({0,1,1,3,2,4});
  assert((compatible({P,Q})==std::set<int>{P,Q}));assert(privateCount(P,{Q})==7&&privateCount(Q,{P})==7);assert(!solve({P,Q,0},{6,6,0},2));
  int A=index({0,0,1,2,3,4}),C=index({0,3,1,2,4,1});
  std::vector<int> B={index({0,1,2,3,2,4}),index({0,1,2,3,3,4}),index({0,1,2,4,3,4})};
  assert((compatible({A,C,B[0],B[1],B[2]})==std::set<int>{A,C,B[0],B[1],B[2]}));
  assert(privateCount(A,{C,B[0],B[1],B[2]})==5);assert(privateCount(C,{A,B[0],B[1],B[2]})==6);
  for(int b:B)assert(privateCount(b,{A,C})==6);
  int distributions=0;for(int x=0;x<=5;++x)for(int y=0;y<=5-x;++y)++distributions;assert(distributions==21);
  std::cout<<"Two-variety obstruction, all five pair witnesses, and 21-member fourteen-cube family verified"<<std::endl;
  if (!triples) return 0;
  long long supports=0,collections=0,failures=0;
  #pragma omp parallel for schedule(dynamic) reduction(+:supports,collections,failures)
  for(int a=0;a<75;++a)for(int b=a+1;b<75;++b)for(int c=b+1;c<75;++c) {
    ++supports;std::vector<Demand> targets;
    for(int t=0;t<75;++t){auto d=demand(t,{a,b,c},3,1);if(!d.need[0])targets.push_back(d);}
    for(int x=1;x<=18;++x)for(int y=1;y<20-x;++y) {
      ++collections;std::array<int,3> counts={x,y,20-x-y};bool yes=false;
      for(const auto& d:targets)if(feasible(d,counts,3)){yes=true;break;}
      if(!yes){++failures;
        #pragma omp critical
        std::cerr<<"FAIL frame: "<<a<<" "<<b<<" "<<c<<" counts "<<x<<" "<<y<<" "<<20-x-y<<std::endl;
      }
    }
  }
  for(int a=0;a<75;++a){assert(solve({a,0,0},{20,0,0},1,1));for(int b=a+1;b<75;++b)for(int x=1;x<20;++x)assert(solve({a,b,0},{x,20-x,0},2,1));}
  std::cout<<"Three-variety 3-frame audit: "<<supports<<" supports, "<<collections<<" positive multiplicity collections, "<<failures<<" failures; smaller supports also checked"<<std::endl;
  assert(supports==67525&&collections==67525LL*171&&failures==0);
}
