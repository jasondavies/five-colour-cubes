// Small replay checker: no search, propagation heuristics or matching algorithm.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <iterator>
#include <vector>
#include <omp.h>

constexpr int n=75;
using Vector=std::array<int,n>;
struct Box {Vector lower{},upper{};};
struct Mask {uint64_t a=0,b=0;};
std::array<std::array<Mask,256>,n> neighbours;
struct Checker {
    std::vector<unsigned char> data;
    size_t position=0;
    unsigned long long commands=0,leaves=0;
    int goal=0,budget=0;Vector bad{};
    int byte(){return position<data.size()?data[position++]:-1;}
    bool excluded(const Box &box,int reason) {
        int lower=0,upper=0,badlower=0;
        for(int i=0;i<n;++i){lower+=box.lower[i];upper+=box.upper[i];badlower+=bad[i]*box.lower[i];}
        if(reason==0)return lower>goal||upper<goal;
        if(reason==1) {
            int outside=0;for(int i=0;i<n;++i)if(!bad[i])outside+=box.upper[i];
            return badlower>budget||outside+budget<goal;
        }
        if(reason<2||reason>=n+2)return false;
        // Encode integer bounds as seven indicator layers, solely to sum a subset.
        std::array<Mask,7> lb{},ub{};
        for(int i=0;i<n;++i) {
            for(int k=0;k<box.lower[i];++k)
                (i<64?lb[k].a:lb[k].b)|=uint64_t(1)<<(i%64);
            for(int k=0;k<box.upper[i];++k)
                (i<64?ub[k].a:ub[k].b)|=uint64_t(1)<<(i%64);
        }
        for(unsigned d=1;d<256;++d) {
            auto mask=neighbours[reason-2][d];int insideLower=0,insideUpper=0;
            for(int k=0;k<7;++k) {
                insideLower+=std::popcount(mask.a&lb[k].a)+std::popcount(mask.b&lb[k].b);
                insideUpper+=std::popcount(mask.a&ub[k].a)+std::popcount(mask.b&ub[k].b);
            }
            int rhs=std::popcount(d)-1;
            // A Hall deficiency could survive only if BOTH inequalities hold.
            if(insideLower<=rhs && goal<=upper-insideUpper+rhs)return false;
        }
        return true;
    }
    bool refine(Box &box,int reason) {
        int lower=0,upper=0;
        for(int i=0;i<n;++i){lower+=box.lower[i];upper+=box.upper[i];}
        Box result=box;
        if(reason==0) {
            if(lower>goal||upper<goal)return false;
            for(int i=0;i<n;++i) {
                result.lower[i]=std::max(box.lower[i],goal-upper+box.upper[i]);
                result.upper[i]=std::min(box.upper[i],goal-lower+box.lower[i]);
            }
        } else if(reason==1) {
            int insideLower=0,outsideUpper=0;
            for(int i=0;i<n;++i)if(bad[i])insideLower+=box.lower[i];else outsideUpper+=box.upper[i];
            if(insideLower>budget||outsideUpper+budget<goal)return false;
            for(int i=0;i<n;++i) {
                if(bad[i])result.upper[i]=std::min(box.upper[i],budget-insideLower+box.lower[i]);
                else result.lower[i]=std::max(box.lower[i],goal-budget-outsideUpper+box.upper[i]);
            }
        } else {
            if(reason<2||reason>=n+2)return false;
            std::array<Mask,7> lb{},ub{};
            for(int i=0;i<n;++i) {
                for(int k=0;k<box.lower[i];++k)(i<64?lb[k].a:lb[k].b)|=uint64_t(1)<<(i%64);
                for(int k=0;k<box.upper[i];++k)(i<64?ub[k].a:ub[k].b)|=uint64_t(1)<<(i%64);
            }
            Mask common{~uint64_t(0),~uint64_t(0)},united{};
            int slack=-1,need=1000;
            for(unsigned d=1;d<256;++d) {
                Mask m=neighbours[reason-2][d];int il=0,iu=0;
                for(int k=0;k<7;++k) {
                    il+=std::popcount(m.a&lb[k].a)+std::popcount(m.b&lb[k].b);
                    iu+=std::popcount(m.a&ub[k].a)+std::popcount(m.b&ub[k].b);
                }
                int rhs=std::popcount(d)-1,ou=upper-iu;
                if(il>rhs||ou+rhs<goal)continue;
                common.a&=m.a;common.b&=m.b;united.a|=m.a;united.b|=m.b;
                slack=std::max(slack,rhs-il);need=std::min(need,goal-rhs-ou);
            }
            if(slack<0)return false;
            for(int i=0;i<n;++i) {
                uint64_t bit=uint64_t(1)<<(i%64);
                if((i<64?common.a:common.b)&bit)result.upper[i]=std::min(box.upper[i],box.lower[i]+slack);
                if(!((i<64?united.a:united.b)&bit))result.lower[i]=std::max(box.lower[i],box.upper[i]+need);
            }
        }
        bool changed=false;
        for(int i=0;i<n;++i) {
            if(result.lower[i]<box.lower[i]||result.upper[i]>box.upper[i]||result.lower[i]>result.upper[i])return false;
            changed|=result.lower[i]!=box.lower[i]||result.upper[i]!=box.upper[i];
        }
        box=result;return changed;
    }
    bool tree(Box box) {
        while(true) {
            ++commands;int op=byte();
            if(op==0){++leaves;return excluded(box,byte());}
            if(op==2){if(!refine(box,byte()))return false;continue;}
            if(op!=1)return false;
            int i=byte(),value=byte();
            if(i<0||i>=n||value<box.lower[i]||value>=box.upper[i])return false;
            Box left=box;left.upper[i]=value;
            box.lower[i]=value+1;
            return tree(left)&&tree(box);
        }
    }
    bool run(const std::string &path,const std::array<int,156> &expected) {
        std::ifstream in(path,std::ios::binary);if(!in)return false;
        data.assign(std::istreambuf_iterator<char>(in),{});
        for(int c:std::string("Q5P2"))if(byte()!=c)return false;
        for(int c:expected)if(byte()!=c)return false;
        int m=expected[1],anchor=expected[4];goal=expected[3];budget=expected[5];
        if(m<1||m>7||anchor<0||anchor>=n||budget<0||budget>7)return false;
        Box root;
        for(int i=0;i<n;++i) {
            root.upper[i]=expected[6+i];bad[i]=expected[81+i];
            if(root.upper[i]<0||root.upper[i]>7||bad[i]<0||bad[i]>1)return false;
        }
        if(root.upper[anchor]!=0||bad[anchor]!=0)return false;
        root.lower[anchor]=root.upper[anchor]=m;
        return tree(root)&&position==data.size();
    }
};
int main(int argc,char**argv) {
    if(argc!=6){std::cerr<<"GEOMETRY CASES PREFIX OUTPUT THREADS\n";return 1;}
    std::ifstream geometry(argv[1]);int size,x;geometry>>size;if(size!=n)return 1;
    for(int j=0;j<n*6;++j)geometry>>x;
    for(int t=0;t<n;++t)for(int i=0;i<n;++i) {
        geometry>>x;if(x<0||x>255)return 1;
        for(int d=1;d<256;++d)if(x&d)
            (i<64?neighbours[t][d].a:neighbours[t][d].b)|=uint64_t(1)<<(i%64);
    }
    if(!geometry)return 1;
    std::ifstream casesFile(argv[2]);int count;casesFile>>count;if(!casesFile||count<0)return 1;
    std::vector<std::array<int,156>> cases(count);
    for(auto &row:cases)for(int &v:row)casesFile>>v;
    if(!casesFile)return 1;
    std::ofstream out(argv[4]);if(!out)return 1;
    out<<"[\n";bool first=true;int rejected=0;
    #pragma omp parallel for schedule(dynamic) num_threads(std::stoi(argv[5])) reduction(+:rejected)
    for(int i=0;i<count;++i) {
        Checker check;bool accepted=check.run(std::string(argv[3])+std::to_string(i)+".q5p",cases[i]);
        if(!accepted)++rejected;
        #pragma omp critical
        {
            if(!first)out<<",\n";
            first=false;
            out<<"{\"case\":"<<i<<",\"accepted\":"<<(accepted?"true":"false")
               <<",\"bytes\":"<<check.data.size()<<",\"commands\":"<<check.commands
               <<",\"leaves\":"<<check.leaves<<'}';
            std::cout<<i<<' '<<(accepted?"VERIFIED":"REJECTED")<<" commands="<<check.commands<<std::endl;
        }
    }
    out<<"\n]\n";return rejected||!out;
}
