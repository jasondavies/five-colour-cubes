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
void inspect(){
 int zero=0;for(int j=1;j<20;j++)if(!(cuts[j]&cuts[0]))zero+=g[j];
 if(zero>5)return;
 for(auto [j,k]:pairs)if(g[j]+g[k]>7)return;
 uint64_t code=canonical();if(!seen.insert(code).second)return;raw++;
 for(int t=0;t<15;t++)if(matches(t))return;
 oppfail++;
 oppoutput<<'[';for(int j=0;j<20;j++){if(j)oppoutput<<',';oppoutput<<g[j];}oppoutput<<"]\n";
 for(int j=0;j<20;j++)if(g[j]>=4 && (matches(15+j,j)||matches(15+(j^1),j)))return;
 loopfail++;
 uint32_t cover=0;for(int j=0;j<20;j++)if(g[j])cover|=cuts[j];
 bool sup=false;for(auto o:opposite)if((cover&o)==o){sup=true;break;}
 if(!sup)return;supported++;
 output<<'[';for(int j=0;j<20;j++){if(j)output<<',';output<<g[j];}output<<"]\n";
}
void allocate(vector<int>&eligible,int i,int rem){
 if(i==(int)eligible.size()){if(!rem)inspect();return;}
 int j=eligible[i],cap=(cuts[j]&cuts[0])?4:3;
 for(int n=0;n<=min(cap,rem);n++){g[j]=n;allocate(eligible,i+1,rem-n);}g[j]=0;
}
void family(uint32_t cover,int exceptions){
 vector<int> eligible,other;for(int j=1;j<20;j++)(((cuts[j]&cuts[0])&~cover)?other:eligible).push_back(j);
 if(!exceptions){allocate(eligible,0,10);return;}
 if(exceptions==1){for(int j:other){g[j]=1;allocate(eligible,0,9);g[j]=0;}return;}
 for(int j:other)for(int k:other)if(j<=k){g[j]++;g[k]++;allocate(eligible,0,8);g[j]--;g[k]--;}
}
int main(){
 geometry();g[0]=4;output.open("research/pure_supported/g4-after-loops.jsonl");oppoutput.open("research/pure_supported/g4-opposite-fails.jsonl");
 vector<pair<string,uint32_t>> triples={{"row",arc(0,2)|arc(0,3)|arc(0,4)},
 {"hook",arc(0,2)|arc(0,3)|arc(1,2)}, {"disjoint",arc(0,2)|arc(0,3)|arc(1,4)}};
 for(auto [name,c]:triples){family(c,0);cerr<<name<<' '<<raw<<' '<<oppfail<<' '<<loopfail<<' '<<supported<<'\n';}
 vector<pair<string,uint32_t>> pp={{"row+one",arc(0,2)|arc(0,3)}, {"column+one",arc(0,2)|arc(1,2)}, {"diagonal+one",arc(0,2)|arc(1,3)}};
 for(auto [name,c]:pp){family(c,1);cerr<<name<<' '<<raw<<' '<<oppfail<<' '<<loopfail<<' '<<supported<<'\n';}
 family(arc(0,2),2);cerr<<"one+two "<<raw<<' '<<oppfail<<' '<<loopfail<<' '<<supported<<'\n';
 cout<<"stabilizer "<<stabilizer.size()<<" unique_profiles "<<raw<<" opposite_fail "<<oppfail<<" no_heavy_loop "<<loopfail<<" supported "<<supported<<'\n';
}
