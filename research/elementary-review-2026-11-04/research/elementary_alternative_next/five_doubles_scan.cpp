// Discovery only: five distinct adjacent classes, each doubled.
#define main unused_g3_main
#include "../root/g3_nonprivate.cpp"
#undef main
long long tested=0,failures5=0;
void choose5(int s,int left){
 if(!left){
  tested++;for(int t=0;t<15;t++)if(matches(t))return;failures5++;
  output<<'[';bool sep=false;for(int j=0;j<20;j++)if(g[j]){if(sep)output<<',';sep=true;output<<j;}output<<"]\n";return;
 }
 for(int j=s;j<20;j++){g[j]=2;choose5(j+1,left-1);g[j]=0;}
}
int main(){geometry();output.open("research/elementary_alternative_next/five-doubles-opposite-fails.jsonl");choose5(0,5);cout<<"tested "<<tested<<" failed "<<failures5<<'\n';}
