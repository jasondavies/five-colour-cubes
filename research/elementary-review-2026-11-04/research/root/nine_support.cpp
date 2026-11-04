// Exploratory exact sweep of pure fourteen-pools with maximum class count four.
// Anchor class0 has four copies. Konig covers the other ten sources by at
// most three corner vertices/source exceptions. This is discovery code only.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <set>
#include <string>
#include <unordered_set>
#include <vector>
using namespace std;
array<uint32_t,20> cuts;
array<uint32_t,15> opposite;
array<array<unsigned,20>,35> masks;
array<int,20> g{};
vector<pair<int,int>> pairs;
vector<array<int,20>> stabilizer;
unordered_set<uint64_t> seen;
long long raw=0,oppfail=0,loopfail=0,supported=0;
ofstream output;
ofstream oppoutput;
uint32_t arc(int a,int b){return 1u<<(5*a+b);}

void geometry(){
 int j=0;for(int a=0;a<5;a++)for(int b=a+1;b<5;b++)for(int r=0;r<2;r++){
  uint32_t m=0;for(int u:{a,b})for(int v=0;v<5;v++)if(v!=a&&v!=b)m|=r?arc(v,u):arc(u,v);cuts[j++]=m;
 }
 j=0;for(int r=0;r<5;r++){
  vector<int> left;for(int v=0;v<5;v++)if(v!=r)left.push_back(v);
  for(int k=1;k<4;k++){
   uint32_t m=0;for(int u:{left[0],left[k]})for(int v:left)if(v!=left[0]&&v!=left[k])m|=arc(u,v)|arc(v,u);opposite[j++]=m;
  }
 }
 for(int t=0;t<35;t++)for(int s=0;s<20;s++){
  uint32_t target=t<15?opposite[t]:cuts[t-15];unsigned m=0;int k=0;
  for(int e=0;e<25;e++)if(target>>e&1){if(cuts[s]>>e&1)m|=1u<<k;k++;}masks[t][s]=m;
 }
 for(int j=0;j<20;j++)for(int k=j+1;k<20;k++)if(popcount(cuts[j]&cuts[k])==4 || (j/2==k/2))pairs.emplace_back(j,k);
 array<int,5> p={0,1,2,3,4};do{
  if((p[0]<2)!=(p[1]<2) || p[0]>=2)continue;
  array<int,20> tr{};for(int j=0;j<20;j++){
   uint32_t m=0;for(int a=0;a<5;a++)for(int b=0;b<5;b++)if(cuts[j]&arc(a,b))m|=arc(p[a],p[b]);
   tr[j]=find(cuts.begin(),cuts.end(),m)-cuts.begin();
  }stabilizer.push_back(tr);
 }while(next_permutation(p.begin(),p.end()));
}
uint64_t canonical(){
 uint64_t best=~uint64_t(0);
 for(auto &p:stabilizer){uint64_t code=0;for(int j=0;j<20;j++)code|=uint64_t(g[j])<<(3*p[j]);best=min(best,code);}return best;
}
bool matches(int t,int exclude=-1){
 unsigned ms[14];int n=0;for(int j=0;j<20;j++)for(int k=0;k<g[j]-(j==exclude?2:0);k++)ms[n++]=masks[t][j];
 int owner[14];fill(owner,owner+n,-1);
 auto aug=[&](auto&& self,int c,unsigned &visited)->bool{
  for(int i=0;i<n;i++)if((ms[i]>>c&1)&&!(visited>>i&1)){
   visited|=1u<<i;if(owner[i]<0 || self(self,owner[i],visited)){owner[i]=c;return true;}}
  return false;
 };
 int need=t<15?8:6;for(int c=0;c<need;c++){unsigned visited=0;if(!aug(aug,c,visited))return false;}return true;
}

int main(){geometry();long long no2=0,no3=0;ofstream out("research/root/nine-no2-support.jsonl");for(unsigned bits=0;bits<(1u<<20);bits++){if(popcount(bits)!=9)continue;int deg[25]={};for(int j=0;j<20;j++)if(bits>>j&1)for(int e=0;e<25;e++)if(cuts[j]>>e&1)deg[e]++;bool got2=false,got3=false;for(auto T:opposite){int mn=20;for(int e=0;e<25;e++)if(T>>e&1)mn=min(mn,deg[e]);if(mn>=2)got2=true;if(mn>=3)got3=true;}if(!got2){no2++;out<<'[';bool first=true;for(int j=0;j<20;j++)if(bits>>j&1){if(!first)out<<',';first=false;out<<j;}out<<"]\n";}if(!got3)no3++;}cout<<"no2 "<<no2<<" no3 "<<no3<<'\n';}