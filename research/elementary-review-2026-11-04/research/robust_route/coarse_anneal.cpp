#include <array>
#include <vector>
#include <bit>
#include <fstream>
#include <iostream>
#include <random>
#include <cmath>
#include <chrono>
#include <set>
using namespace std;
array<array<unsigned,20>,35> fits;
vector<pair<int,int>> sharedfour;
array<int,14> cubes;
array<int,20> counts;
array<int,20> poles;
int N=14;
array<array<vector<int>,20>,20> candidates;
bool tri_match(int t,int j,int k){
 vector<unsigned> masks;for(int s=0;s<20;s++)for(int n=0;n<counts[s]-(s==j)-(s==k);n++)masks.push_back(fits[15+t][s]);
 vector<int>owner(masks.size(),-1);
 auto aug=[&](auto&&self,int corner,unsigned&seen)->bool{
  for(int i=0;i<(int)masks.size();i++)if((masks[i]>>corner&1)&&!(seen>>i&1)){
   seen|=1u<<i;if(owner[i]<0||self(self,owner[i],seen)){owner[i]=corner;return true;}}
  return false;
 };
 for(int c=0;c<6;c++){unsigned seen=0;if(!aug(aug,c,seen))return false;}return true;
}
bool six_clique(){
 unsigned edges[20]={};int weight[20]={};unsigned active=0;
 for(int j=0;j<20;j++)if(counts[j]){
  active|=1u<<j;weight[j]=1;
  for(int k=j;k<20;k++)if(counts[k]&&(j!=k||counts[j]>1)){
   bool ok=false;for(int t:candidates[j][k])if(tri_match(t,j,k)){ok=true;break;}
   if(ok){if(j==k)weight[j]=counts[j];else{edges[j]|=1u<<k;edges[k]|=1u<<j;}}
  }
 }
 auto rec=[&](auto&&self,unsigned remaining,int total,int common)->bool{
  while(remaining){int j=countr_zero(remaining);remaining&=remaining-1;int p=common&poles[j];
   if(total+weight[j]+popcount((unsigned)p)>5)return true;
   if(self(self,remaining&edges[j],total+weight[j],p))return true;}
  return false;
 };
 return rec(rec,active,0,31);
}
bool augment(int t,int c,array<int,8>& owner,unsigned& seen){
 unsigned opts=fits[t][cubes[c]]&~seen;
 while(opts){int k=countr_zero(opts);opts&=opts-1;if(seen>>k&1)continue;seen|=1u<<k;
  if(owner[k]<0||augment(t,owner[k],owner,seen)){owner[k]=c;return true;}}
 return false;
}
bool matches(int t){array<int,8>owner;owner.fill(-1);int rank=0;
 for(int c=0;c<N&&rank<8;c++){unsigned seen=0;if(augment(t,c,owner,seen))rank++;}return rank==8;}
bool robust(int j){int sub[64]={};for(int i=0;i<20;i++)sub[fits[15+j][i]]+=counts[i];
 for(int k=0;k<6;k++)for(int m=0;m<64;m++)if(m>>k&1)sub[m]+=sub[m^(1<<k)];
 for(int m=1;m<64;m++)if(N-sub[63^m]<popcount((unsigned)m)+2)return false;return true;
}
int cost(){int score=0;unsigned covered=0;for(int c:cubes)covered|=fits[0][c];score+=8*(8-popcount(covered));
 for(int t=0;t<15;t++)score+=matches(t);
 unsigned R=0;vector<int> robust3;
 for(int j=0;j<20;j++)if(robust(j)){R|=1u<<(j/2);if(counts[j]>=4)score++;if(counts[j]==3)robust3.push_back(j);}
 for(int j=0;j<20;j++)if(counts[j]){
  int allowed=31^poles[j];
  for(int k:robust3)if(j!=k&&poles[j]&poles[k])allowed&=poles[k]&~poles[j];
  if(!allowed || (counts[j]==3 && find(robust3.begin(),robust3.end(),j)!=robust3.end() && popcount((unsigned)allowed)<3))score++;
 }
 // Every robust spanning bipartite graph permits <=4 crossing sources.
 for(int A=1;A<16;A++){int B=31^A;bool complete=true;int mass=0;
  for(int j=0;j<20;j+=2)if((poles[j]&A)&&(poles[j]&B)){
   if(!(R>>(j/2)&1)){complete=false;break;}mass+=counts[j]+counts[j+1];}
  if(complete&&mass>4)score++;
 }
 if(!score&&six_clique())score++;
 return score;
}
bool caps(){for(int x:counts)if(x>5)return false;for(auto[a,b]:sharedfour)if(counts[a]+counts[b]>7)return false;for(int j=0;j<20;j+=2)if(counts[j]+counts[j+1]>7)return false;return true;}
int main(int argc,char**argv){int seconds=argc>1?atoi(argv[1]):40;ifstream in("research/coarse_computation/coarse_data.txt");for(auto&r:fits)for(auto&v:r)in>>v;int n;in>>n;for(int k=0;k<n;k++){int a,b;in>>a>>b;sharedfour.emplace_back(a,b);}int k=0;for(int a=0;a<5;a++)for(int b=a+1;b<5;b++){poles[k++]=(1<<a)|(1<<b);poles[k++]=(1<<a)|(1<<b);}
 for(int j=0;j<20;j++)for(int k=j;k<20;k++)for(int t=0;t<20;t++){
  int p=poles[t],a=countr_zero((unsigned)p),b=countr_zero((unsigned)(p^(1<<a)));
  if(((poles[j]>>a&1)&&(poles[k]>>b&1))||((poles[j]>>b&1)&&(poles[k]>>a&1)))candidates[j][k].push_back(t);}
 mt19937 rng(381919);long long it=0;int best=1000;auto start=chrono::steady_clock::now();
 for(int restart=0;;restart++){do{counts.fill(0);for(int&c:cubes){c=rng()%20;counts[c]++;}}while(!caps());int score=cost();
  for(int k=0;k<10000;k++){it++;int at=rng()%N,old=cubes[at],next=rng()%20;counts[old]--;counts[next]++;cubes[at]=next;int s=caps()?cost():1000;double temp=.05+.6*(1.-double(k)/10000);if(s<=score||generate_canonical<double,53>(rng)<exp((score-s)/temp))score=s;else{counts[old]++;counts[next]--;cubes[at]=old;}if(score<best){best=score;cerr<<"best "<<best<<" it "<<it<<'\n';}if(score==0){cout<<"COUNTER";for(int c:counts)cout<<' '<<c;cout<<'\n';cout<<"robust";for(int j=0;j<20;j++)if(robust(j))cout<<' '<<j;cout<<'\n';return 0;}if((it&1023)==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>seconds){cout<<"TIME best "<<best<<" iterations "<<it<<'\n';return 0;}}
 }
}
