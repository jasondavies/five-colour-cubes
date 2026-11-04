// Standalone exact finite check; not a substitute for an elementary proof.
// Claim: an eight-cube pool with at least five opposite-repeat cubes, with
// each opposite variety used at most twice, has an opposite target unless
// exactly three cubes are adjacent-repeat and all have one tricolour class.
// Compile: c++ -O3 -std=c++20 diffuse_eight_cube_check.cpp -o diffuse_check
#include <algorithm>
#include <array>
#include <bit>
#include <cstdlib>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
using Inventory = std::array<unsigned char,15>;
std::array<std::uint32_t,35> sources;
std::array<std::array<unsigned char,35>,15> masks;
std::vector<std::array<int,15>> symmetries;
std::set<Inventory> cores;
std::array<int,8> cubes;
std::uint32_t arc(int a,int b) { return 1u<<(5*a+b); }

void geometry() {
  int j=0;
  for(int a=0;a<5;a++) for(int b=a+1;b<5;b++) for(int reverse=0;reverse<2;reverse++) {
    std::uint32_t s=0;
    for(int u:{a,b}) for(int v=0;v<5;v++) if(v!=a&&v!=b)
      s|=reverse?arc(v,u):arc(u,v);
    sources[j++]=s;
  }
  for(int r=0;r<5;r++) {
    std::vector<int> left; for(int v=0;v<5;v++) if(v!=r) left.push_back(v);
    for(int k=1;k<4;k++) {
      std::uint32_t s=0;
      for(int u:{left[0],left[k]}) for(int v:left) if(v!=left[0]&&v!=left[k])
        s|=arc(u,v)|arc(v,u);
      sources[j++]=s;
    }
  }
  for(int t=0;t<15;t++) for(int s=0;s<35;s++) {
    int k=0;unsigned m=0;
    for(int e=0;e<25;e++) if(sources[20+t]>>e&1) {
      if(sources[s]>>e&1) m|=1u<<k;
      k++;
    }
    masks[t][s]=m;
  }
  std::array<int,5> p={0,1,2,3,4};
  do {
    std::array<int,15> permutation{};
    for(int s=0;s<15;s++) {
      std::uint32_t image=0;
      for(int a=0;a<5;a++) for(int b=0;b<5;b++) if(sources[20+s]&arc(a,b))
        image|=arc(p[a],p[b]);
      permutation[s]=std::find(sources.begin()+20,sources.end(),image)-(sources.begin()+20);
      if(permutation[s]>=15) std::abort();
    }
    symmetries.push_back(permutation);
  } while(std::next_permutation(p.begin(),p.end()));
}

void enumerate_cores(Inventory& x,int i,int remaining) {
  if(i==15) {
    if(remaining) return;
    Inventory best=x;
    for(const auto& p:symmetries) {
      Inventory y{}; for(int j=0;j<15;j++) y[p[j]]=x[j];
      best=std::min(best,y);
    }
    cores.insert(best); return;
  }
  for(int n=0;n<=std::min(2,remaining);n++) { x[i]=n;enumerate_cores(x,i+1,remaining-n); }
}

bool augment(int target,int corner,std::array<int,8>& owner,unsigned& seen) {
  for(int i=0;i<8;i++) if((masks[target][cubes[i]]>>corner&1)&&!(seen>>i&1)) {
    seen|=1u<<i;
    if(owner[i]<0||augment(target,owner[i],owner,seen)) { owner[i]=corner; return true; }
  }
  return false;
}


std::array<bool,15> solved{};
std::array<int,15> scores{};
bool has_opposite_target() {
 bool answer=false;
 for(int t=0;t<15;t++) {
  scores[t]=0;for(int s:cubes)scores[t]+=std::popcount(masks[t][s]);
  std::array<int,8> owner;owner.fill(-1);bool matched=true;
  for(int corner=0;corner<8;corner++){unsigned seen=0;if(!augment(t,corner,owner,seen)){matched=false;break;}}
  solved[t]=matched;answer|=matched;
 }
 return answer;
}

int main() {
  geometry();Inventory zero{};enumerate_cores(zero,0,5);
  std::uint64_t checked=0,exceptions=0,maxbad=0,maxallbad=0;
  for(const auto& x:cores) {
    int at=0;for(int i=0;i<15;i++) for(int k=0;k<x[i];k++) cubes[at++]=20+i;
    for(int a=0;a<35;a++) for(int b=a;b<35;b++) for(int c=b;c<35;c++) {
      Inventory total=x;for(int s:{a,b,c}) if(s>=20) total[s-20]++;
      if(*std::max_element(total.begin(),total.end())>2) continue;
      cubes[5]=a;cubes[6]=b;cubes[7]=c;checked++;
      if(has_opposite_target()) {
        int best=*std::max_element(scores.begin(),scores.end());bool some=false,bad=false;
        for(int t=0;t<15;t++)if(scores[t]==best){some|=solved[t];bad|=!solved[t];}
        maxbad+=bad;
        if(!some){maxallbad++;if(maxallbad<3){std::cout<<"badmax ";for(auto c:cubes)std::cout<<c<<" ";std::cout<<"score "<<best<<"\n";}}
        continue;
      }
      exceptions++;
      if(!(a<20&&a==b&&b==c)) { std::cerr<<"Unexpected counterexample\n";return 1; }
    }
  }
  std::cout<<"Five-opposite colour orbits: "<<cores.size()<<"\n";
  std::cout<<"Eight-cube checks with global opposite cap2: "<<checked<<"\n";
  std::cout<<"Exceptions (all three adjacent sources share a class): "<<exceptions<<"\n";
  std::cout<<"Maxscore has a failure "<<maxbad<<"; all fail "<<maxallbad<<"\n";
}
