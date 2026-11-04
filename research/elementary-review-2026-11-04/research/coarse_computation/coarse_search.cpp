#include <array>
#include <vector>
#include <bit>
#include <fstream>
#include <iostream>
#include <random>
#include <cmath>
#include <chrono>
using namespace std;
array<array<unsigned,20>,35>fits;
vector<pair<int,int>>pairs;
array<int,14>cubes;
array<int,20>counts;
bool augment(int t,int c,array<int,8>&owner,unsigned&seen){unsigned opts=fits[t][cubes[c]]&~seen;while(opts){int k=countr_zero(opts);opts&=opts-1;if(seen>>k&1)continue;seen|=1u<<k;if(owner[k]<0||augment(t,owner[k],owner,seen)){owner[k]=c;return true;}}return false;}
int matching_rank(int t,int exclude,int cap){array<int,8>owner;owner.fill(-1);int matching_rank=0;for(int c=0;c<14&&matching_rank<cap;c++)if(cubes[c]!=exclude){unsigned seen=0;if(augment(t,c,owner,seen))matching_rank++;}return matching_rank;}
int cost(){int score=0;unsigned covered=0;for(int c:cubes)covered|=fits[0][c];score+=8*(8-popcount(covered));for(int t=0;t<15;t++)score+=(matching_rank(t,-1,8)==8);for(int j=0;j<20;j++)if(counts[j]>=4)score+=(matching_rank(15+j,j,8-counts[j])>=8-counts[j]);return score;}
bool caps(){for(int x:counts)if(x>5)return false;for(auto[a,b]:pairs)if(counts[a]+counts[b]>7)return false;return true;}
int main(){ifstream in("coarse_data.txt");for(auto&r:fits)for(auto&v:r)in>>v;int n;in>>n;for(int k=0;k<n;k++){int a,b;in>>a>>b;pairs.emplace_back(a,b);}mt19937 rng(19191);long long it=0;int best=1000;auto start=chrono::steady_clock::now();
 for(int restart=0;;restart++){do{counts.fill(0);for(int&c:cubes){c=rng()%20;counts[c]++;}}while(!caps());int score=cost();
 for(int k=0;k<50000;k++){it++;int at=rng()%14,old=cubes[at],next=rng()%20;counts[old]--;counts[next]++;cubes[at]=next;int s=caps()?cost():1000;double temp=.05+.6*(1.-double(k)/50000);if(s<=score||generate_canonical<double,53>(rng)<exp((score-s)/temp))score=s;else{counts[old]++;counts[next]--;cubes[at]=old;}if(score<best){best=score;cerr<<"best "<<best<<" it "<<it<<'\n';}if(score==0){cout<<"COUNTER";for(int c:counts)cout<<' '<<c;cout<<'\n';return 0;}if((it&4095)==0&&chrono::duration<double>(chrono::steady_clock::now()-start).count()>60){cout<<"TIME best "<<best<<'\n';return 0;}}
 }
}
