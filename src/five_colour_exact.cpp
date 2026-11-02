// Complete bounded DFS, with incremental matching and monotone candidate pruning.
// Each exported case fixes a most frequent variety and one of its Hall covers.
#include "five_colour_matching.hpp"
#include <algorithm>
#include <chrono>
#include <fstream>
#include <iostream>
#include <numeric>
#include <omp.h>

struct Case {
    int kind,m,cover,goal,anchor,budget;
    std::array<int,N> cap,bad;
};
struct Search {
    Case c;
    double limit;
    std::chrono::steady_clock::time_point start;
    unsigned long long nodes=0;
    bool timed_out=false,found=false;
    std::vector<int> witness;
    double elapsed() const { return std::chrono::duration<double>(
        std::chrono::steady_clock::now()-start).count(); }
    void visit(const State &s, const std::vector<int> &candidates,
               const std::array<int,N> &left, int budget) {
        if (timed_out || found) return;
        if ((++nodes & 4095)==0 && elapsed()>limit) { timed_out=true;return; }
        int need=c.goal-static_cast<int>(s.cubes.size());
        if (need==0) { found=true;witness=s.cubes;return; }
        int good_capacity=0,bad_capacity=0;
        for (int i:candidates) (c.bad[i]?bad_capacity:good_capacity)+=left[i];
        if (good_capacity+std::min(bad_capacity,budget)<need) return;
        std::vector<int> valid;
        std::vector<State> next_states;
        auto tight=left;
        good_capacity=bad_capacity=0;
        for (int i:candidates) {
            if (left[i]==0 || (c.bad[i] && budget==0)) continue;
            State next=s;
            if (next.add(i)) {
                int maximum=1;
                State repeated=next;
                int bound=std::min(left[i],c.bad[i]?budget:left[i]);
                while (maximum<bound && repeated.add(i)) ++maximum;
                tight[i]=maximum;
                valid.push_back(i);next_states.push_back(std::move(next));
                (c.bad[i]?bad_capacity:good_capacity)+=tight[i];
            }
        }
        if (good_capacity+std::min(bad_capacity,budget)<need) return;
        // Partition candidates into groups whose distinct members cannot coexist.
        // A completion takes copies from at most one type in each such group.
        if (s.cubes.size()>=7) {
            std::vector<std::vector<unsigned>> groups;
            std::vector<int> weights;
            int bound=0;
            for (unsigned j=0;j<valid.size();++j) {
                bool placed=false;
                for (unsigned g=0;g<groups.size() && !placed;++g) {
                    bool incompatible=true;
                    for (unsigned k:groups[g]) {
                        State pair=next_states[j];
                        if (pair.add(valid[k])) { incompatible=false;break; }
                    }
                    if (incompatible) {
                        groups[g].push_back(j);
                        int weight=std::max(weights[g],tight[valid[j]]);
                        bound+=weight-weights[g];weights[g]=weight;placed=true;
                    }
                }
                if (!placed) {
                    groups.push_back({j});weights.push_back(tight[valid[j]]);
                    bound+=weights.back();
                }
                if (bound>=need) break;
            }
            if (bound<need) return;
        }
        for (unsigned j=0;j<valid.size();++j) {
            int i=valid[j];
            auto remaining=tight;--remaining[i];
            std::vector<int> tail(valid.begin()+j,valid.end());
            visit(next_states[j],tail,remaining,budget-c.bad[i]);
            if (timed_out || found) return;
        }
    }
    void run() {
        start=std::chrono::steady_clock::now();
        State s;
        for (int j=0;j<c.m;++j) if (!s.add(c.anchor)) std::abort();
        std::vector<int> candidates;
        for (int i=0;i<N;++i) if (c.cap[i]) candidates.push_back(i);
        // A fixed per-case order avoids duplicate multisets. Constrained types first.
        std::stable_sort(candidates.begin(),candidates.end(),[&](int i,int j) {
            return c.bad[i]>c.bad[j];
        });
        visit(s,candidates,c.cap,c.budget);
    }
};

int main(int argc,char **argv) {
    if (argc!=6) { std::cerr<<"GEOMETRY CASES OUTPUT SECONDS_PER_CASE THREADS\n";return 1; }
    std::ifstream in(argv[1]);int n;
    if (!(in>>n) || n!=N) return 1;
    for (auto &r:faces) for (auto &x:r) in>>x;
    for (auto &r:fits) for (auto &x:r) in>>x;
    if (!in) return 1;
    std::ifstream input(argv[2]);int count;
    if (!(input>>count) || count<0) return 1;
    std::vector<Case> cases(count);
    for (auto &c:cases) {
        input>>c.kind>>c.m>>c.cover>>c.goal>>c.anchor>>c.budget;
        for (int &x:c.cap) input>>x;
        for (int &x:c.bad) input>>x;
    }
    if (!input) return 1;
    std::ofstream out(argv[3]);out<<"[\n";bool first=true;
    #pragma omp parallel for schedule(dynamic) num_threads(std::stoi(argv[5]))
    for (int q=0;q<count;++q) {
        Search s{cases[q],std::stod(argv[4]),{},0,false,false,{}};
        s.run();
        const char *status=s.found?"SAT":s.timed_out?"UNKNOWN":"EXHAUSTIVE_UNSAT";
        #pragma omp critical
        {
            if (!first) out<<",\n";
            first=false;
            out<<"{\"case\":"<<q<<",\"kind\":"<<s.c.kind<<",\"m\":"<<s.c.m
               <<",\"size_requested\":"<<s.c.goal
               <<",\"cover\":"<<s.c.cover<<",\"status\":\""<<status
               <<"\",\"nodes\":"<<s.nodes<<",\"seconds\":"<<s.elapsed();
            if (s.found) {
                out<<",\"copies\":[";
                for (unsigned j=0;j<s.witness.size();++j) out<<(j?",":"")<<s.witness[j];
                out<<']';
            }
            out<<'}';out.flush();
            std::cout<<q<<' '<<s.c.m<<' '<<s.c.kind<<' '<<s.c.cover<<' '<<status
                     <<" nodes="<<s.nodes<<" seconds="<<s.elapsed()<<std::endl;
        }
    }
    out<<"\n]\n";
    return !out;
}
