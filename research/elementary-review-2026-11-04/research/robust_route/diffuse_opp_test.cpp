#include <array>
#include <algorithm>
#include <vector>
#include <set>
#include <fstream>
#include <iostream>
#include <cstdint>
using namespace std;
array<array<unsigned char,35>,15> fits;
array<array<int,15>,120> syms;
using Inventory=array<unsigned char,15>;
set<Inventory> orbits;
Inventory cur{};
void rec(int i,int rem){
 if(i==15){if(rem)return;Inventory best=cur;
  for(auto&p:syms){Inventory y{};for(int j=0;j<15;j++)y[p[j]]=cur[j];best=min(best,y);}orbits.insert(best);return;}
 for(int x=0;x<=min(2,rem);x++){cur[i]=x;rec(i+1,rem-x);}
}
array<int,8> cubes;
bool aug(int t,int c,array<int,8>&owner,unsigned&seen){
 for(int i=0;i<8;i++)if((fits[t][cubes[i]]>>c&1)&&!(seen>>i&1)){
  seen|=1u<<i;if(owner[i]<0||aug(t,owner[i],owner,seen)){owner[i]=c;return true;}}
 return false;
}
bool solves(){
 for(int t=0;t<15;t++){array<int,8>owner;owner.fill(-1);bool yes=true;
  for(int c=0;c<8;c++){unsigned seen=0;if(!aug(t,c,owner,seen)){yes=false;break;}}
  if(yes)return true;}
 return false;
}
int main(){
 ifstream in("research/robust_route/opp_mix_data.txt");int v;
 for(auto&r:fits)for(auto&m:r){in>>v;m=v;}
 for(auto&p:syms)for(auto&v:p)in>>v;
 rec(0,5);cout<<"opposite_5_orbits="<<orbits.size()<<endl;
 uint64_t tests=0,fail=0;ofstream out("research/robust_route/diffuse_opp_failures.txt");
 for(auto&x:orbits){int pos=0;for(int i=0;i<15;i++)for(int k=0;k<x[i];k++)cubes[pos++]=20+i;
  for(int a=0;a<35;a++)for(int b=a;b<35;b++)for(int c=b;c<35;c++){
   cubes[5]=a;cubes[6]=b;cubes[7]=c;tests++;
   if(!solves()){fail++;for(auto n:x)out<<(int)n<<' ';out<<a<<' '<<b<<' '<<c<<'\n';}
  }
 }
 cout<<"tests="<<tests<<" failures="<<fail<<endl;
}
