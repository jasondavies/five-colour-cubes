#include <array>
#include <vector>
#include <fstream>
#include <iostream>
#include <algorithm>
using namespace std;
vector<array<int,4>> cy(15);
struct Cut{int neigh,rhs;};
vector<Cut> cuts[15];
array<int,15>x{};long long total=0,failed=0;int maxprint=10,N;
bool solves(){
 for(int t=0;t<15;t++){
  bool good=true;
  for(auto c:cuts[t]){int s=0;for(int i=0;i<15;i++)if(c.neigh>>i&1)s+=x[i];if(s<=c.rhs){good=false;break;}}
  if(good)return true;
 }
 return false;
}
void rec(int at,int remain){
 if(at==14){x[at]=remain;++total;if(!solves()){++failed;if(maxprint-->0){cout<<"fail";for(auto a:x)cout<<' '<<a;cout<<'\n';}}return;}
 for(int n=0;n<=remain;n++){x[at]=n;rec(at+1,remain-n);}
}
int main(int argc,char**argv){
 N=argc>1?atoi(argv[1]):8;
 ifstream in("opp_data.txt");for(auto &c:cy)for(int &e:c)in>>e;
 for(int t=0;t<15;t++)for(int s=1;s<16;s++){
 int mask=0;for(int i=0;i<15;i++)for(int k=0;k<4;k++)if(s>>k&1)if(find(cy[i].begin(),cy[i].end(),cy[t][k])!=cy[i].end()){mask|=1<<i;break;}
 cuts[t].push_back({mask,2*__builtin_popcount((unsigned)s)-1});}
 rec(0,N);cout<<"N "<<N<<" total "<<total<<" failed "<<failed<<'\n';
}
