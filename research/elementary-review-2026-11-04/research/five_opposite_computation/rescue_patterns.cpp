// Discovery only: rescue corners for five capped opposite sources + two copies of C(01).
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <vector>
using namespace std;
array<uint32_t,35> source;
array<array<uint8_t,35>,15> mask;
array<array<int,8>,15> arcs;
vector<array<int,25>> sym;
array<int,15> inv{};
array<int,7> pieces;
map<uint32_t,vector<array<int,15>>> patterns;
uint32_t arc(int a,int b){return 1u<<(5*a+b);}
void geometry(){
 int j=0;for(int a=0;a<5;a++)for(int b=a+1;b<5;b++)for(int rev=0;rev<2;rev++){
  for(int u:{a,b})for(int v=0;v<5;v++)if(v!=a&&v!=b)source[j]|=rev?arc(v,u):arc(u,v);j++;
 }
 for(int r=0;r<5;r++){vector<int> v;for(int a=0;a<5;a++)if(a!=r)v.push_back(a);
  for(int k=1;k<4;k++){for(int a:{v[0],v[k]})for(int b:v)if(b!=v[0]&&b!=v[k])source[j]|=arc(a,b)|arc(b,a);j++;}}
 for(int t=0;t<15;t++){int k=0;for(int e=0;e<25;e++)if(source[20+t]>>e&1){arcs[t][k]=e;for(int s=0;s<35;s++)if(source[s]>>e&1)mask[t][s]|=1u<<k;k++;}}
 array<int,5> p={0,1,2,3,4};do{if(p[0]>=2||p[1]>=2)continue;array<int,25> tr;for(int a=0;a<5;a++)for(int b=0;b<5;b++)tr[5*a+b]=5*p[a]+p[b];sym.push_back(tr);}while(next_permutation(p.begin(),p.end()));
}
bool fill_except(int t,int hole){
 int owner[7];fill(owner,owner+7,-1);
 auto aug=[&](auto&& self,int c,unsigned& seen)->bool{
  for(int p=0;p<7;p++)if((mask[t][pieces[p]]>>c&1)&&!(seen>>p&1)){seen|=1u<<p;if(owner[p]<0||self(self,owner[p],seen)){owner[p]=c;return true;}}
  return false;};
 for(int c=0;c<8;c++)if(c!=hole){unsigned seen=0;if(!aug(aug,c,seen))return false;}return true;
}
uint32_t canon(uint32_t e){uint32_t best=~0u;for(auto&p:sym){uint32_t x=0;for(int k=0;k<25;k++)if(e>>k&1)x|=1u<<p[k];best=min(best,x);}return best;}
void examine(){int k=0;for(int j=0;j<15;j++)for(int z=0;z<inv[j];z++)pieces[k++]=20+j;pieces[5]=pieces[6]=0;
 uint32_t e=0;for(int t=0;t<15;t++)for(int h=0;h<8;h++)if(fill_except(t,h))e|=1u<<arcs[t][h];
 patterns[e].push_back(inv);
}
void rec(int j,int left){if(j==15){if(!left)examine();return;}for(int c=0;c<=min(2,left);c++){inv[j]=c;rec(j+1,left-c);}inv[j]=0;}
void writepat(ostream& out,uint32_t e,const vector<array<int,15>>& cores){out<<"{\"mask\":"<<e<<",\"arcs\":[";bool sep=false;for(int k=0;k<25;k++)if(e>>k&1){if(sep)out<<',';sep=true;out<<'['<<k/5<<','<<k%5<<']';}out<<"],\"cores\":"<<cores.size()<<",\"example\":[";for(int j=0;j<15;j++){if(j)out<<',';out<<cores.front()[j];}out<<"],\"avoiding_classes\":[";sep=false;for(int j=0;j<20;j++)if(!(source[j]&e)){if(sep)out<<',';sep=true;out<<j;}out<<"]}";}
int main(int argc,char**argv){geometry();rec(0,5);if(argc>1){int d=atoi(argv[1]);for(auto it=patterns.begin();it!=patterns.end();){auto &v=it->second;v.erase(remove_if(v.begin(),v.end(),[&](auto &x){return count(x.begin(),x.end(),2)!=d;}),v.end());if(v.empty())it=patterns.erase(it);else ++it;}}map<uint32_t,vector<array<int,15>>> orbits;long long count=0;for(auto&[e,c]:patterns){count+=c.size();auto&v=orbits[canon(e)];v.insert(v.end(),c.begin(),c.end());}
 // Orbit representatives only record an untransformed example: canonical masks and examples may differ by symmetry.
 ofstream out("research/five_opposite_computation/rescue-patterns"+string(argc>1?argv[1]:"")+".jsonl");for(auto&[e,c]:patterns){writepat(out,e,c);out<<'\n';}
 map<int,int> hist;for(auto&[e,c]:patterns)hist[popcount(e)]+=c.size();cout<<"cores "<<count<<" patterns "<<patterns.size()<<" orbits "<<orbits.size()<<'\n';for(auto&[n,c]:hist)cout<<"size "<<n<<": "<<c<<'\n';
 vector<uint32_t> minimal;for(auto&[e,c]:patterns){bool min=true;for(auto&[f,d]:patterns)if(e!=f&&(f&~e)==0){min=false;break;}if(min)minimal.push_back(e);}
 set<uint32_t> minorb;for(auto e:minimal)minorb.insert(canon(e));cout<<"minimal patterns "<<minimal.size()<<" orbits "<<minorb.size()<<'\n';for(auto e:minorb){writepat(cout,e,patterns[e]);cout<<'\n';}
}
