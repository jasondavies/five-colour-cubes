// Discovery sweep: g0=3, all g<=3, no loop at class0, at most one private corner.
// Konig covers outside incidences with at most four vertices.
// Four-corner/no-exception covers have >=2 private corners and are excluded.
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
 int zero=0;uint32_t others=0;
 for(int j=1;j<20;j++)if(g[j]){others|=cuts[j];if(!(cuts[j]&cuts[0]))zero+=g[j];}
 if(zero>5||popcount(cuts[0]&~others)>1)return;
 uint64_t code=canonical();if(!seen.insert(code).second)return;raw++;
 if(matches(15,0)||matches(16,0))return;
 loopfail++;
 for(int t=0;t<15;t++)if(matches(t))return;
 oppfail++;
 output<<'[';for(int j=0;j<20;j++){if(j)output<<',';output<<g[j];}output<<"]\n";
}
void allocate(vector<int>&eligible,int i,int rem){
 if(i==(int)eligible.size()){if(!rem)inspect();return;}
 if(rem>3*((int)eligible.size()-i))return;
 int j=eligible[i];
 for(int n=0;n<=min(3,rem);n++){g[j]=n;allocate(eligible,i+1,rem-n);}g[j]=0;
}
void exceptions_rec(vector<int>&eligible,vector<int>&other,int start,int left,int total){
 if(!left){allocate(eligible,0,11-total);return;}
 for(int i=start;i<(int)other.size();i++)if(g[other[i]]<3){g[other[i]]++;exceptions_rec(eligible,other,i,left-1,total);g[other[i]]--;}
}
void family(uint32_t cover,int exceptions){
 vector<int> eligible,other;for(int j=1;j<20;j++)(((cuts[j]&cuts[0])&~cover)?other:eligible).push_back(j);
 exceptions_rec(eligible,other,0,exceptions,exceptions);
}
int main(){
 geometry();g[0]=3;output.open("research/root/g3-nonloop-nonprivate.jsonl");
 vector<pair<string,uint32_t>> triples={{"row",arc(0,2)|arc(0,3)|arc(0,4)},
 {"hook",arc(0,2)|arc(0,3)|arc(1,2)}, {"disjoint",arc(0,2)|arc(0,3)|arc(1,4)}};
 for(auto [name,c]:triples){family(c,1);cerr<<name<<' '<<raw<<' '<<loopfail<<' '<<oppfail<<'\n';}
 vector<pair<string,uint32_t>> pp={{"row+two",arc(0,2)|arc(0,3)}, {"column+two",arc(0,2)|arc(1,2)}, {"diagonal+two",arc(0,2)|arc(1,3)}};
 for(auto [name,c]:pp){family(c,2);cerr<<name<<' '<<raw<<' '<<loopfail<<' '<<oppfail<<'\n';}
 family(arc(0,2),3);cerr<<"one+three "<<raw<<' '<<loopfail<<' '<<oppfail<<'\n';
 cout<<"unique_profiles "<<raw<<" anchor_nonloop "<<loopfail<<" opposite_fail "<<oppfail<<'\n';
}
