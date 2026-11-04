// Discovery only: consequences of the hand nine-distinct, six-repeated,
// and three-copy/private-corner lemmas, anchored at an own-loop A^3.
#define main old_discovery_main
#include "../root/g3_nonprivate.cpp"
#undef main
#include <map>

long long visited2=0, own2=0, ofail2=0, private2=0, pole2=0;
map<int,long long> triple_hist;
ofstream candidates2;

void inspect2(){
 visited2++;
 if(!matches(15,0))return;
 own2++;
 for(int t=0;t<15;t++)if(matches(t))return;
 ofail2++;
 vector<int> owntriples;
 for(int j=0;j<20;j++)if(g[j]==3){
  if(matches(15+j,j))owntriples.push_back(j);
  else{
   uint32_t other=0;for(int k=0;k<20;k++)if(k!=j&&g[k])other|=cuts[k];
   if(popcount(cuts[j]&~other)<2)return;
  }
 }
 private2++;
 // Own-loop triples require disjoint pole pairs.
 for(int j:owntriples)for(int k:owntriples)if(j<k){
  // Poles are recovered from the class-index order below.
  int ja=0,jb=0,ka=0,kb=0,ix=0;
  for(int a=0;a<5;a++)for(int b=a+1;b<5;b++,ix++){
   if(j/2==ix){ja=a;jb=b;}if(k/2==ix){ka=a;kb=b;}
  }
  if(ja==ka||ja==kb||jb==ka||jb==kb)return;
 }
 pole2++;triple_hist[(int)owntriples.size()]++;
 candidates2<<'[';for(int j=0;j<20;j++){if(j)candidates2<<',';candidates2<<g[j];}candidates2<<"]\n";
}

void allocate2(int j,int rem,int active,int repeated){
 if(!rem){inspect2();return;}
 if(j==20||active==8||rem>3*(8-active)||repeated>5)return;
 if(j==1){allocate2(j+1,rem,active,repeated);return;}
 for(int n=0;n<=min(3,rem);n++){
  if(repeated+(n>=2)>5)continue;
  g[j]=n;allocate2(j+1,rem-n,active+(n>0),repeated+(n>=2));
 }
 g[j]=0;
}

int main(){
 geometry();g[0]=3;
 candidates2.open("research/pure_supported/own-loop-candidates.jsonl");
 allocate2(1,11,1,1);
 candidates2.close();
 cerr<<"visited "<<visited2<<" own "<<own2<<" O-fail "<<ofail2
     <<" private "<<private2<<" poles "<<pole2<<'\n';
 for(auto [t,n]:triple_hist)cerr<<"own triples "<<t<<": "<<n<<'\n';
 return 0;
}
