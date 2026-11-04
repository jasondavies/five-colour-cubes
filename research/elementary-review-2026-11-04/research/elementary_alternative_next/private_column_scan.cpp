// Discovery only: normalized private column and one avoiding opposite.
#define main unused_old_scan_main
#include "../root/g3_nonprivate.cpp"
#undef main
bool with_opposite(int t, int source) {
 unsigned ms[15]; int n=0;
 for(int j=0;j<20;j++)for(int k=0;k<g[j];k++)ms[n++]=masks[t][j];
 uint32_t target=opposite[t];unsigned m=0;int k=0;
 for(int e=0;e<25;e++)if(target>>e&1){if(opposite[source]>>e&1)m|=1u<<k;k++;}
 ms[n++]=m;int owner[15];fill(owner,owner+n,-1);
 auto aug=[&](auto&& self,int c,unsigned& seen)->bool{
  for(int i=0;i<n;i++)if((ms[i]>>c&1)&&!(seen>>i&1)){seen|=1u<<i;if(owner[i]<0||self(self,owner[i],seen)){owner[i]=c;return true;}}
  return false;
 };
 for(int c=0;c<8;c++){unsigned seen=0;if(!aug(aug,c,seen))return false;}return true;
}
long long eligible_count=0,pure_failure_count=0;
bool high_only=false;
array<long long,15> failures{};
void scan_profile(){
 eligible_count++;
 for(int t=0;t<15;t++)if((!high_only||t==6||t==9||t==12)&&matches(t))return;
 pure_failure_count++;
 uint32_t unionothers=0;for(int j=1;j<20;j++)if(g[j])unionothers|=cuts[j];
 int private_count=popcount(cuts[0]&~unionothers);
 for(int o:{0,3,6,7,8}){
  bool ok=false;for(int t=0;t<15;t++)if((!high_only||t==6||t==9||t==12)&&with_opposite(t,o)){ok=true;break;}
  if(ok)continue;
  failures[o]++;
  output<<"{\"g\":[";for(int j=0;j<20;j++){if(j)output<<',';output<<g[j];}
  output<<"],\"o\":"<<o+60<<",\"private_count\":"<<private_count<<"}\n";
 }
}
void gen_scan(const vector<int>& eligible,int i,int left,int occ,int rep){
 if(i==(int)eligible.size()){if(!left)scan_profile();return;}
 if(left>3*((int)eligible.size()-i))return;
 int j=eligible[i];
 for(int n=0;n<=min(3,left);n++)if(occ+(n>0)<=8&&rep+(n>=2)<=5){g[j]=n;gen_scan(eligible,i+1,left-n,occ+(n>0),rep+(n>=2));}
 g[j]=0;
}
int main(int argc,char**argv){high_only=argc>1;geometry();g[0]=3;vector<int> eligible;uint32_t column=arc(0,2)|arc(1,2);for(int j=1;j<20;j++)if(!(cuts[j]&column))eligible.push_back(j);output.open(string("research/elementary_alternative_next/private-column-added-opposite-fails")+(high_only?"-high":"")+".jsonl");gen_scan(eligible,0,11,1,1);cout<<"profiles "<<eligible_count<<" pureopfail "<<pure_failure_count<<'\n';for(int o:{0,3,6,7,8})cout<<o+60<<" fails "<<failures[o]<<'\n';}
