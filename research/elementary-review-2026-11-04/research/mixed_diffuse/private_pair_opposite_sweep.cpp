// Discovery only. Normalize a nonloop triple and one of its private pairs.
// All output is coarse; no finite search result is used as a hand lemma.
#define main previous_discovery_main
#include "../root/g3_nonprivate.cpp"
#undef main
#include <map>

long long profiles = 0, private_ok = 0, opposite_fail = 0;
array<long long, 15> avoidance{}, residual{};
ofstream records;

bool with_opposite(int t, int source) {
  unsigned ms[15]; int n = 0;
  for (int j=0;j<20;j++) for(int k=0;k<g[j];k++) ms[n++]=masks[t][j];
  uint32_t target = opposite[t]; unsigned m=0; int k=0;
  for(int e=0;e<25;e++) if(target>>e&1) {
    if(opposite[source]>>e&1)m|=1u<<k;
    k++;
  }
  ms[n++]=m;
  int owner[15]; fill(owner,owner+n,-1);
  auto aug=[&](auto&& self,int c,unsigned& seen)->bool{
    for(int i=0;i<n;i++)if((ms[i]>>c&1)&&!(seen>>i&1)){
      seen|=1u<<i;
      if(owner[i]<0||self(self,owner[i],seen)){owner[i]=c;return true;}
    }return false;
  };
  for(int c=0;c<8;c++){unsigned seen=0;if(!aug(aug,c,seen))return false;}
  return true;
}

void inspect_profile() {
  profiles++;
  int loops=0; uint32_t private_union=0;
  for(int j=0;j<20;j++)if(g[j]==3){
    uint32_t other=0;
    for(int k=0;k<20;k++)if(k!=j&&g[k])other|=cuts[k];
    uint32_t priv=cuts[j]&~other;
    if(popcount(priv)<2){
      if(!matches(15+j,j)||++loops>1)return;
    } else {
      if(popcount(priv)!=2)return;
      vector<pair<int,int>> e;
      for(int a=0;a<5;a++)for(int b=0;b<5;b++)if(priv&arc(a,b))e.emplace_back(a,b);
      // A row means a common endpoint on the two-element side of the cut.
      if(j%2==0 ? e[0].first==e[1].first : e[0].second==e[1].second)return;
      private_union|=priv;
    }
  }
  if(loops!=1)return;
  private_ok++;
  for(int t=0;t<15;t++)if(matches(t))return;
  opposite_fail++;
  records<<"{\"g\":[";
  for(int j=0;j<20;j++){if(j)records<<',';records<<g[j];}
  records<<"],\"avoiding\":[";
  bool first=true;
  for(int o=0;o<15;o++)if(!(opposite[o]&private_union)){
    avoidance[o]++;
    if(!first)records<<',';first=false;records<<o+60;
    bool solved=false;
    for(int t=0;t<15;t++)if(with_opposite(t,o)){solved=true;break;}
    if(!solved)residual[o]++;
  }
  records<<"]}\n";
}

void allocate_profile(const vector<int>& eligible,int i,int left,int occupied,int repeated){
  if(i==(int)eligible.size()){if(!left)inspect_profile();return;}
  if(left>3*((int)eligible.size()-i))return;
  int j=eligible[i];
  for(int n=0;n<=min(3,left);n++){
    if(occupied+(n>0)>8||repeated+(n>=2)>5)continue;
    g[j]=n;allocate_profile(eligible,i+1,left-n,occupied+(n>0),repeated+(n>=2));
  }
  g[j]=0;
}

int main(int argc,char** argv){
  geometry();g[0]=3;
  bool diagonal=argc>1&&string(argv[1])=="diagonal";
  uint32_t priv=arc(0,2)|arc(1,diagonal?3:2);
  vector<int> eligible;
  for(int j=1;j<20;j++)if(!(cuts[j]&priv))eligible.push_back(j);
  records.open(string("research/mixed_diffuse/")+(diagonal?"private-diagonal":"private-column")+"-opposite-discovery.jsonl");
  allocate_profile(eligible,0,11,1,1);
  cout<<"profiles "<<profiles<<" private_ok "<<private_ok<<" opposite_fail "<<opposite_fail<<'\n';
  for(int o=0;o<15;o++)if(avoidance[o])cout<<o+60<<' '<<avoidance[o]<<' '<<residual[o]<<'\n';
}
