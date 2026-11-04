// Discovery only: three opposite sources, cap two; adjacent classes, cap three.
// Extensions of a prefix admitting an opposite assembly are pruned by monotonicity.
#include <algorithm>
#include <array>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <vector>
using namespace std;
using Inventory=array<unsigned char,15>;
array<uint32_t,35> source{};
array<array<uint8_t,35>,15> fits{};
vector<array<int,15>> sym;
set<Inventory> cores;
Inventory inv{};
array<int,20> g{};
array<int,15> pieces{};
array<long long,13> fail{},nodes{},sol{};
map<vector<int>,long long> profiles[13];
int limit=11,coreidx=0,selected=-1;
ofstream out;
uint32_t arc(int a,int b){return 1u<<(5*a+b);}
void geometry(){
 int j=0;
 for(int a=0;a<5;a++)for(int b=a+1;b<5;b++)for(int rev=0;rev<2;rev++){
  for(int u:{a,b})for(int v=0;v<5;v++)if(v!=a&&v!=b)source[j]|=rev?arc(v,u):arc(u,v);
  j++;
 }
 for(int r=0;r<5;r++){
  vector<int> v;for(int a=0;a<5;a++)if(a!=r)v.push_back(a);
  for(int k=1;k<4;k++){
   for(int a:{v[0],v[k]})for(int b:v)if(b!=v[0]&&b!=v[k])source[j]|=arc(a,b)|arc(b,a);
   j++;
  }
 }
 for(int t=0;t<15;t++){
  int k=0;for(int e=0;e<25;e++)if(source[20+t]>>e&1){
   for(int s=0;s<35;s++)if(source[s]>>e&1)fits[t][s]|=1u<<k;
   k++;
  }
 }
 array<int,5> p={0,1,2,3,4};
 do{
  array<int,15> tr;
  for(int j=0;j<15;j++){
   uint32_t m=0;
   for(int a=0;a<5;a++)for(int b=0;b<5;b++)if(source[20+j]&arc(a,b))m|=arc(p[a],p[b]);
   tr[j]=find(source.begin()+20,source.end(),m)-(source.begin()+20);
  }
  sym.push_back(tr);
 }while(next_permutation(p.begin(),p.end()));
}
void enumerate(int j,int left){
 if(j==15){
  if(left)return;
  Inventory best=inv;
  for(auto&p:sym){Inventory x{};for(int i=0;i<15;i++)x[p[i]]=inv[i];best=min(best,x);}
  cores.insert(best);return;
 }
 for(int n=0;n<=min(2,left);n++){inv[j]=n;enumerate(j+1,left-n);}
 inv[j]=0;
}
bool solves(int n){
 for(int t=0;t<15;t++){
  unsigned uni=0;for(int i=0;i<n;i++)uni|=fits[t][pieces[i]];
  if(uni!=255)continue;
  int owner[15];fill(owner,owner+n,-1);
  auto aug=[&](auto&& self,int c,unsigned& seen)->bool{
   for(int i=0;i<n;i++)if((fits[t][pieces[i]]>>c&1)&&!(seen>>i&1)){
    seen|=1u<<i;
    if(owner[i]<0||self(self,owner[i],seen)){owner[i]=c;return true;}
   }
   return false;
  };
  bool ok=true;
  for(int c=0;c<8;c++){unsigned seen=0;if(!aug(aug,c,seen)){ok=false;break;}}
  if(ok)return true;
 }
 return false;
}
void record(){
 out<<"{\"core\":"<<coreidx<<",\"opposite\":[";
 for(int j=0;j<15;j++){if(j)out<<',';out<<int(inv[j]);}
 out<<"],\"adjacent\":[";for(int j=0;j<20;j++){if(j)out<<',';out<<g[j];}
 out<<"]}\n";
}
void dfs(int start,int n){
 nodes[n]++;
 if(n>=5&&solves(n+3)){sol[n]++;return;}
 fail[n]++;
 if(n>=5){vector<int> p;for(int x:g)if(x)p.push_back(x);sort(p.begin(),p.end(),greater<int>());profiles[n][p]++;}
 if(n==limit){record();return;}
 for(int j=start;j<20;j++)if(g[j]<3){pieces[3+n]=j;g[j]++;dfs(j,n+1);g[j]--;}
}
int main(int argc,char**argv){
 if(argc>1)limit=atoi(argv[1]);if(argc>2)selected=atoi(argv[2]);
 if(limit<5||limit>12)return 2;
 geometry();enumerate(0,3);
 cerr<<"Opposite orbits "<<cores.size()<<'\n';
 string suffix=to_string(limit)+(selected>=0?"-core"+to_string(selected):"");
 out.open("research/three_opposite_root/opposite-fails-"+suffix+".jsonl");
 for(auto x:cores){
  inv=x;
  if(selected>=0&&selected!=coreidx){coreidx++;continue;}
  int k=0;for(int i=0;i<15;i++)for(int n=0;n<inv[i];n++)pieces[k++]=20+i;
  cerr<<"Core "<<coreidx<<" sources";for(int i=0;i<15;i++)if(inv[i])cerr<<' '<<60+i<<':'<<int(inv[i]);cerr<<'\n';
  auto prev=fail[limit];dfs(0,0);
  cerr<<"Core "<<coreidx++<<" leaf failures "<<fail[limit]-prev<<'\n';
 }
 for(int n=0;n<=limit;n++){
  cout<<"n "<<n<<" visited "<<nodes[n]<<" solved "<<sol[n]<<" failed "<<fail[n]<<'\n';
  if(n==limit)for(auto&[p,v]:profiles[n]){cout<<" profile";for(auto a:p)cout<<' '<<a;cout<<": "<<v<<'\n';}
 }
}
