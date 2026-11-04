#include <algorithm>
#include <array>
#include <iostream>
#include <vector>
#include "tri_model.inc"

bool matching(const std::array<int,20>&g,int t) {
    int cm[14],assigned[14],size=0;
    for(int j=0;j<20;++j)for(int k=0;k<g[j];++k)cm[size++]=masks[t][j];
    std::fill(assigned,assigned+14,-1);
    auto augment=[&](auto&&self,int corner,int&seen)->bool {
        for(int i=0;i<14;++i)if((cm[i]>>corner&1)&&!(seen>>i&1)) {
            seen|=1<<i;
            if(assigned[i]<0||self(self,assigned[i],seen)){assigned[i]=corner;return true;}
        }
        return false;
    };
    for(int k=0;k<8;++k){int seen=0;if(!augment(augment,k,seen))return false;}
    return true;
}
int main(){
    int count=0;std::array<int,20>g{};
    for(int a=0;a<20;++a)for(int b=a+1;b<20;++b)for(int c=b+1;c<20;++c)for(int d=c+1;d<20;++d){
        g[a]=g[b]=g[c]=g[d]=3;
        for(int e=0;e<20;++e)if(!g[e])for(int f=e+1;f<20;++f)if(!g[f]){
            g[e]=g[f]=1;bool fail=true;
            for(int t=0;t<15;++t)if(matching(g,t)){fail=false;break;}
            if(fail){++count;std::cout<<a<<' '<<b<<' '<<c<<' '<<d<<" | "<<e<<' '<<f<<'\n';}
            g[e]=g[f]=0;
        }
        g[a]=g[b]=g[c]=g[d]=0;
    }
    std::cerr<<"all-O-failing configurations: "<<count<<'\n';
}
