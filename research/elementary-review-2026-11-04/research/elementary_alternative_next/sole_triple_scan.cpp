// Discovery only: profile 3,2,2,2,2,1,1,1 with the triple normalized.
#define main unused_g3_main
#include "../root/g3_nonprivate.cpp"
#undef main
long long count_all=0,count_fail=0;
void record_profile(){
 count_all++;
 for(int t=0;t<15;t++)if(matches(t))return;
 count_fail++;
 output<<"[";for(int j=0;j<20;j++){if(j)output<<',';output<<g[j];}output<<"]\n";
}
void singles(int s,int left){if(!left){record_profile();return;}for(int j=s;j<20;j++)if(!g[j]){g[j]=1;singles(j+1,left-1);g[j]=0;}}
void doubles(int s,int left){if(!left){singles(1,3);return;}for(int j=s;j<20;j++){g[j]=2;doubles(j+1,left-1);g[j]=0;}}
int main(){geometry();g[0]=3;output.open("research/elementary_alternative_next/sole-triple-opposite-fails.jsonl");doubles(1,4);cout<<"checked "<<count_all<<" opposite_fail "<<count_fail<<'\n';}
