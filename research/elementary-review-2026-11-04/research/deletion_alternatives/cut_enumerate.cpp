#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <set>
#include <string>
#include <vector>

using Inventory=std::array<unsigned char,20>;
std::vector<int> cuts;
std::array<uint32_t,20> arcs;
std::vector<std::array<int,20>> symmetries;
std::array<std::array<unsigned char,20>,20> incidence;

int cut_index(int s){return std::find(cuts.begin(),cuts.end(),s)-cuts.begin();}
void setup(){
  for(int s=0;s<32;++s) if(std::popcount((unsigned)s)==2||std::popcount((unsigned)s)==3) cuts.push_back(s);
  for(int i=0;i<20;++i){int bit=0;arcs[i]=0;
    for(int a=0;a<5;++a)for(int b=0;b<5;++b)if(a!=b){
      if((cuts[i]>>a&1)&&!(cuts[i]>>b&1))arcs[i]|=1u<<bit;
      ++bit;
    }
  }
  std::array<int,5> p={0,1,2,3,4};
  do {for(int flip=0;flip<2;++flip){
    std::array<int,20> perm;
    for(int i=0;i<20;++i){int s=0;for(int a=0;a<5;++a)if(cuts[i]>>a&1)s|=1<<p[a];if(flip)s^=31;perm[i]=cut_index(s);}
    symmetries.push_back(perm);
  }}while(std::next_permutation(p.begin(),p.end()));
  for(int t=0;t<20;++t)for(int s=0;s<20;++s){int k=0;unsigned char m=0;
    for(int e=0;e<20;++e)if(arcs[t]>>e&1){if(arcs[s]>>e&1)m|=1<<k;++k;}
    incidence[t][s]=m;
  }
}
Inventory canonical(const Inventory& x){
  Inventory out=x;
  for(auto& p:symmetries){Inventory y;for(int i=0;i<20;++i)y[p[i]]=x[i];if(y<out)out=y;}
  return out;
}
bool augment(int corner,std::vector<unsigned char>& masks,std::vector<int>& owner,unsigned& seen){
  for(int i=0;i<(int)masks.size();++i)if((masks[i]>>corner&1)&&!(seen>>i&1)){
    seen|=1u<<i;if(owner[i]<0||augment(owner[i],masks,owner,seen)){owner[i]=corner;return true;}
  }
  return false;
}
int solves(const Inventory& x,int margin=0){
  for(int t=0;t<20;++t){
    if(margin){
      int sub[64]={};int total=0;
      for(int s=0;s<20;++s){sub[incidence[t][s]]+=x[s];total+=x[s];}
      for(int k=0;k<6;++k)for(int m=0;m<64;++m)if(m>>k&1)sub[m]+=sub[m^(1<<k)];
      bool yes=true;
      for(unsigned m=1;m<64;++m)if(total-sub[63^m]<(int)std::popcount(m)+margin){yes=false;break;}
      if(yes)return t;
      continue;
    }
    std::vector<unsigned char> masks;
    for(int s=0;s<20;++s)for(int i=0;i<x[s];++i)masks.push_back(incidence[t][s]);
    std::vector<int> owner(masks.size(),-1);bool yes=true;
    for(int k=0;k<6;++k){unsigned seen=0;if(!augment(k,masks,owner,seen)){yes=false;break;}}
    if(yes)return t;
  }
  return -1;
}
int main(int argc,char**argv){
  int bound=argc>1?std::stoi(argv[1]):11;
  int margin=argc>2?std::stoi(argv[2]):0;
  setup();std::set<Inventory> current;Inventory zero{};current.insert(zero);
  for(int n=1;n<=bound;++n){
    std::set<Inventory> next;uint64_t candidates=0,success=0;
    for(auto x:current)for(int s=0;s<20;++s){++x[s];++candidates;
      if(n>=6+margin&&solves(x,margin)>=0)++success;else next.insert(canonical(x));
      --x[s];
    }
    std::cout<<"n="<<n<<" extensions="<<candidates<<" soluble="<<success<<" failure_orbits="<<next.size()<<std::endl;
    if(n>=9&&next.size()<=50){
      for(auto& x:next){std::cout<<"  ";for(int i=0;i<20;++i)if(x[i])std::cout<<cuts[i]<<":"<<(int)x[i]<<" ";std::cout<<"\n";}
    }
    current.swap(next);
    if(current.empty())break;
  }
}
