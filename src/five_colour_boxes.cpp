// Experimental interval proof search. Independent of incremental matchings.
#include <array>
#include <bit>
#include <cstdint>
#include <cstdlib>
#include <vector>
#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <omp.h>

constexpr int N=75;
std::array<std::array<int,6>,N> faces;
std::array<std::array<unsigned,N>,N> fits;
using Bits = __uint128_t;
constexpr Bits all = (Bits(1)<<N)-1;
int population(Bits x) { return std::popcount(static_cast<unsigned long long>(x)) +
    std::popcount(static_cast<unsigned long long>(x>>64)); }
struct Cut { Bits in=0; int rhs; };
std::array<std::vector<Cut>,N> cuts;
struct Box { std::array<int,N> lo{},hi{}; };
struct Case { int kind,m,cover,goal,anchor,budget; std::array<int,N> cap,bad; };
struct Search {
    Case c; double limit; unsigned long long nodes=0,passes=0;
    bool timeout=false,sat=false; Box witness;
    std::ofstream proof;
    int refinement=-1;
    void emit(std::initializer_list<int> bytes) {
        if(!proof.is_open())return;
        for(int v:bytes){if(v<0||v>255)std::abort();proof.put(static_cast<char>(v));}
    }
    void leaf(int reason){emit({0,reason});}
    void narrow(Box &b,int i,int l,int h,int reason,bool &changed) {
        if(l>h)std::abort();
        if(l!=b.lo[i]||h!=b.hi[i]) {
            if(refinement!=reason){emit({2,reason});refinement=reason;}
            b.lo[i]=l;b.hi[i]=h;changed=true;
        }
    }
    std::chrono::steady_clock::time_point start;
    double elapsed() const {return std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();}
    bool linear(Box &b,const std::array<int,N>& in,int rhs,bool &changed) {
        int lower=0,outside=0;
        for(int i=0;i<N;++i)if(in[i])lower+=b.lo[i];else outside+=b.hi[i];
        if(lower>rhs||outside+rhs<c.goal){leaf(1);return false;}
        for(int i=0;i<N;++i) {
            int l=b.lo[i],h=b.hi[i];
            if(in[i])h=std::min(h,rhs-lower+l);
            else l=std::max(l,c.goal-rhs-outside+h);
            narrow(b,i,l,h,1,changed);
        }
        return true;
    }
    bool propagate(Box &b,int &branch) {
        bool changed=true;
        while(changed) {
            if(elapsed()>limit){timeout=true;return false;}
            ++passes;changed=false;refinement=-1;
            if(!linear(b,c.bad,c.budget,changed))return false;
            int low=0,high=0;for(int i=0;i<N;++i){low+=b.lo[i];high+=b.hi[i];}
            if(low>c.goal||high<c.goal){leaf(0);return false;}
            for(int i=0;i<N;++i) {
                int l=std::max(b.lo[i],c.goal-high+b.hi[i]);
                int h=std::min(b.hi[i],c.goal-low+b.lo[i]);
                narrow(b,i,l,h,0,changed);
            }
            if(changed)continue;
            int fewest=256;branch=-1;
            std::array<Bits,7> lowbits{}, highbits{};
            for(int i=0;i<N;++i) {
                for(int j=0;j<b.lo[i];++j)lowbits[j]|=Bits(1)<<i;
                for(int j=0;j<b.hi[i];++j)highbits[j]|=Bits(1)<<i;
            }
            int layers=0;for(int h:b.hi)layers=std::max(layers,h);
            for(int t=0;t<N;++t) {
                Bits intersection=all,united=0;
                int maxslack=-1,minneed=100;
                int viable=0;bool trivial=false;
                for(const Cut &cut:cuts[t]) {
                    int il=0,ih=0;
                    for(int j=0;j<layers;++j) {
                        il+=population(cut.in&lowbits[j]);ih+=population(cut.in&highbits[j]);
                    }
                    int oh=high-ih;
                    if(il>cut.rhs||oh<c.goal-cut.rhs)continue;
                    if(ih<=cut.rhs||c.goal-(low-il)<=cut.rhs){trivial=true;break;}
                    ++viable;intersection&=cut.in;united|=cut.in;
                    maxslack=std::max(maxslack,cut.rhs-il);
                    minneed=std::min(minneed,c.goal-cut.rhs-oh);
                }
                if(trivial)continue;
                if(!viable){leaf(t+2);return false;}
                for(int i=0;i<N;++i) {
                    int l=b.lo[i],h=b.hi[i];
                    if(intersection&(Bits(1)<<i))h=std::min(h,l+maxslack);
                    if(!(united&(Bits(1)<<i)))l=std::max(l,h+minneed);
                    narrow(b,i,l,h,t+2,changed);
                }
                if(changed)break;
                if(viable<fewest) {
                    int best=-1,score=-1;
                    for(int i=0;i<N;++i)if(b.lo[i]<b.hi[i]) {
                        int s=(b.hi[i]-b.lo[i])*(1+int(bool((united^intersection)&(Bits(1)<<i))));
                        if(s>score){score=s;best=i;}
                    }
                    if(best>=0){branch=best;fewest=viable;}
                }
            }
        }
        return true;
    }
    void visit(Box b) {
        if(timeout||sat)return;
        ++nodes;int branch=-1;
        if(!propagate(b,branch))return;
        if(branch<0) {
            for(int i=0;i<N;++i)if(b.lo[i]<b.hi[i]){branch=i;break;}
            if(branch<0){sat=true;witness=b;return;}
        }
        int middle=(b.lo[branch]+b.hi[branch])/2;
        emit({1,branch,middle});
        Box left=b;left.hi[branch]=middle;visit(left);
        b.lo[branch]=middle+1;visit(b);
    }
    void run(const std::string &path) {
        if(!path.empty()) {
            proof.open(path,std::ios::binary);if(!proof)std::abort();
            proof.write("Q5P2",4);
            emit({c.kind,c.m,c.cover,c.goal,c.anchor,c.budget});
            for(int v:c.cap)emit({v});
            for(int v:c.bad)emit({v});
        }
        start=std::chrono::steady_clock::now();Box b;
        b.hi=c.cap;b.lo[c.anchor]=b.hi[c.anchor]=c.m;
        visit(b);
        if(proof.is_open()){proof.flush();if(!proof)std::abort();}
    }
};
int main(int argc,char**argv) {
    if(argc!=6&&argc!=7){std::cerr<<"GEOMETRY CASES OUTPUT SECONDS THREADS [PROOF_PREFIX]\n";return 1;}
    std::ifstream geo(argv[1]);int n;geo>>n;if(n!=N)return 1;
    for(auto&r:faces)for(auto&v:r)geo>>v;
    for(auto&r:fits)for(auto&v:r)geo>>v;
    if(!geo)return 1;
    for(int t=0;t<N;++t)for(unsigned s=1;s<256;++s) {
        Cut cut;cut.rhs=std::popcount(s)-1;
        for(int i=0;i<N;++i)if(fits[t][i]&s)cut.in|=Bits(1)<<i;
        cuts[t].push_back(cut);
    }
    std::ifstream input(argv[2]);int count;input>>count;if(!input||count<0)return 1;
    std::vector<Case> cases(count);
    for(auto&c:cases){input>>c.kind>>c.m>>c.cover>>c.goal>>c.anchor>>c.budget;
        for(int&v:c.cap)input>>v;
        for(int&v:c.bad)input>>v;
    }
    if(!input)return 1;
    std::ofstream out(argv[3]);out<<"[\n";bool first=true;
    #pragma omp parallel for schedule(dynamic) num_threads(std::stoi(argv[5]))
    for(int i=0;i<count;++i) {
        Search s{};s.c=cases[i];s.limit=std::stod(argv[4]);
        s.run(argc==7?std::string(argv[6])+std::to_string(i)+".q5p":"");
        const char*status=s.sat?"SAT":s.timeout?"UNKNOWN":"UNSAT";
        #pragma omp critical
        {
            if(!first)out<<",\n";
            first=false;
            out<<"{\"case\":"<<i<<",\"status\":\""<<status<<"\",\"nodes\":"<<s.nodes
               <<",\"passes\":"<<s.passes<<",\"seconds\":"<<s.elapsed();
            if(s.sat){out<<",\"counts\":[";for(int j=0;j<N;++j)out<<(j?",":"")<<s.witness.lo[j];out<<']';}
            out<<'}';out.flush();
            std::cout<<i<<' '<<status<<" nodes="<<s.nodes<<" seconds="<<s.elapsed()<<std::endl;
        }
    }
    out<<"\n]\n";
}
