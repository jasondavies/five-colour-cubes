#include <algorithm>
#include <array>
#include <fstream>
#include <iostream>
#include <vector>
#include "full_model.inc"
bool matching(const std::array<int,14>&copies,int t) {
    int assigned[14];std::fill(assigned,assigned+14,-1);
    auto augment=[&](auto&&self,int corner,int&seen)->bool {
        for(int i=0;i<14;++i)if((full_masks[t][copies[i]]>>corner&1)&&!(seen>>i&1)) {
            seen|=1<<i;
            if(assigned[i]<0||self(self,assigned[i],seen)){assigned[i]=corner;return true;}
        }
        return false;
    };
    for(int k=0;k<8;++k){int seen=0;if(!augment(augment,k,seen))return false;}
    return true;
}
int main(){
    std::ifstream in("coarse_profile.txt");char bar;int classes[6];std::array<int,14>cp{};
    int configs=0;
    while(in>>classes[0]>>classes[1]>>classes[2]>>classes[3]>>bar>>classes[4]>>classes[5]){
        ++configs;
        for(int r=0;r<729;++r){int value=r,idx=0;
            for(int j=0;j<6;++j){int type=3*classes[j]+value%3;value/=3;int n=j<4?3:1;for(int k=0;k<n;++k)cp[idx++]=type;}
            bool fail=true;
            for(int t=0;t<60;++t)if(matching(cp,t)){fail=false;break;}
            if(fail){std::cout<<"config "<<configs<<'\n';for(int x:cp)std::cout<<x<<' ';std::cout<<'\n';return 0;}
        }
    }
    std::cout<<"none\n";
}
