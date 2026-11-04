#include <array>
#include <vector>
#include <bit>
#include <fstream>
#include <iostream>
#include <random>
#include <cmath>
#include <chrono>
using namespace std;
array<array<int,6>,75> faces;
array<array<unsigned,75>,75> fits;
vector<int> allowed;
array<int,14>cubes;
bool augment(int t,int c,array<int,8>&owner,unsigned&seen){
 unsigned opts=fits[t][cubes[c]]&~seen;
 while(opts){int k=countr_zero(opts);opts&=opts-1;if(seen>>k&1)continue;seen|=1u<<k;
 if(owner[k]<0||augment(t,owner[k],owner,seen)){owner[k]=c;return true;}}
 return false;
}
int cost(){int score=0;for(int t=0;t<75;t++){array<int,8>owner;owner.fill(-1);int rank=0;for(int c=0;c<14&&rank<8;c++){unsigned seen=0;if(augment(t,c,owner,seen))rank++;}score+=(rank==8);}return score;}
int main(int argc,char**argv){ifstream in(argv[1]);int n;in>>n;for(auto&r:faces)for(auto&v:r)in>>v;for(auto&r:fits)for(auto&v:r)in>>v;
 for(int i=0;i<75;i++){bool opp=false;for(int k=0;k<3;k++)opp|=faces[i][2*k]==faces[i][2*k+1];if(!opp)allowed.push_back(i);}
 mt19937 rng(79331);long long it=0;int global=1000;auto start=chrono::steady_clock::now();
 for(int restart=0;;restart++){
  for(int&x:cubes)x=allowed[rng()%60];int score=cost();
  for(int k=0;k<40000;k++){
   it++;int at=rng()%14,old=cubes[at];cubes[at]=allowed[rng()%60];int next=cost();double temp=0.05+0.7*(1.-double(k)/40000);
   if(next<=score||generate_canonical<double,53>(rng)<exp((score-next)/temp))score=next;else cubes[at]=old;
   if(score<global){global=score;cerr<<"best "<<global<<" it "<<it<<'\n';}
   if(score==0){cout<<"FAILURE";for(int c:cubes)cout<<' '<<c;cout<<'\n';return 0;}
   if((it&4095)==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>60){cout<<"TIME best "<<global<<'\n';return 0;}
  }
 }
}
