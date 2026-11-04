// Exploratory exact search of failing extensions of a fixed six-cube core.
// Monotonicity prunes soluble partial inventories. This is not a hand proof.
#include <algorithm>
#include <array>
#include <chrono>
#include <cstdlib>
#include <iostream>
#include <vector>
#include "corner_masks.inc"

std::vector<int> copies;
std::array<unsigned long long, 16> nodes{};
int target_size=12;
bool stopped=false, found=false;
auto started=std::chrono::steady_clock::now();
int seconds_limit=45;
bool require_loops=false;
bool collect_all=false;
int anchor_a=0,anchor_b=0;

bool fits(int t) {
  std::array<unsigned,8> neighbors{};
  for (unsigned p=0;p<8;++p)
    for(unsigned i=0;i<copies.size();++i)
      if(masks[t][copies[i]]&(1u<<p)) neighbors[p]|=1u<<i;
  std::sort(neighbors.begin(),neighbors.end(),[](unsigned a,unsigned b){
    return __builtin_popcount(a)<__builtin_popcount(b);
  });
  if (!neighbors[0]) return false;
  std::array<int,16> owner;owner.fill(-1);
  auto augment=[&](auto&& self,int p,unsigned& seen)->bool {
    unsigned available=neighbors[p]&~seen;
    while(available) {
      unsigned i=__builtin_ctz(available);available&=available-1;seen|=1u<<i;
      if(owner[i]<0||self(self,owner[i],seen)) {owner[i]=p;return true;}
    }
    return false;
  };
  for(int p=0;p<8;++p) {unsigned seen=0;if(!augment(augment,p,seen)) return false;}
  return true;
}
bool soluble() {
  // Opposite targets often solve a diverse extension quickly.
  for(int t=60;t<75;++t) if(fits(t))return true;
  for(int t=0;t<60;++t) if(fits(t))return true;
  return false;
}
bool own_loop(int anchor) {
  auto saved=copies;
  int removed=0;
  copies.erase(std::remove_if(copies.begin(),copies.end(),[&](int s){
    if(s/3==anchor && removed<2){++removed;return true;}
    return false;
  }),copies.end());
  // Tricoloured corners are bits 2..7 in the sorted adjacent-target list.
  std::array<unsigned,6> ns{};
  for(int p=0;p<6;++p)for(unsigned i=0;i<copies.size();++i)
    if(masks[3*anchor][copies[i]]&(1u<<(p+2)))ns[p]|=1u<<i;
  std::sort(ns.begin(),ns.end(),[](unsigned a,unsigned b){return __builtin_popcount(a)<__builtin_popcount(b);});
  std::array<int,16> owner;owner.fill(-1);
  auto augment=[&](auto&&self,int p,unsigned&seen)->bool{
    unsigned av=ns[p]&~seen;
    while(av){unsigned i=__builtin_ctz(av);av&=av-1;seen|=1u<<i;
      if(owner[i]<0||self(self,owner[i],seen)){owner[i]=p;return true;}}
    return false;
  };
  bool ok=true;
  for(int p=0;p<6&&ok;++p){unsigned seen=0;ok=augment(augment,p,seen);}
  copies=saved;return ok;
}
void search(int lower) {
  unsigned size=copies.size();++nodes[size];
  if(size>=8&&soluble())return;
  if(int(size)==target_size) {
    if(require_loops && (!own_loop(anchor_a)||!own_loop(anchor_b)))return;
    found=true;if(!collect_all)stopped=true;std::cout<<"COUNTEREXAMPLE";
    for(auto s:copies)std::cout<<' '<<s;
    std::cout<<'\n';return;
  }
  if((nodes[size]&4095)==0 && std::chrono::steady_clock::now()-started>std::chrono::seconds(seconds_limit)) {
    stopped=true;return;
  }
  for(int s=lower;s<75&&!stopped;++s) {copies.push_back(s);search(s);copies.pop_back();}
}
int main(int argc,char**argv) {
  if(argc<3)return 2;
  int a=std::atoi(argv[1]),b=std::atoi(argv[2]);
  anchor_a=a;anchor_b=b;
  if(argc>3)target_size=std::atoi(argv[3]);
  if(argc>4)seconds_limit=std::atoi(argv[4]);
  if(argc>5)require_loops=std::atoi(argv[5]);
  if(argc>6)collect_all=std::atoi(argv[6]);
  for(int j:{a,b})for(int r=0;r<3;++r)copies.push_back(3*j+r);
  search(0);
  std::cout<<"classes "<<a<<' '<<b<<" size "<<target_size<<" status "
           <<(stopped?(found?"counterexample":"timeout"):(found?"exhausted_with_counterexamples":"exhausted"))<<" nodes";
  for(int i=6;i<=target_size;++i)std::cout<<' '<<nodes[i];
  std::cout<<" seconds "<<std::chrono::duration<double>(std::chrono::steady_clock::now()-started).count()<<'\n';
}
