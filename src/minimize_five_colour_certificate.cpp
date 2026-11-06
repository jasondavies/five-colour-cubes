// Experimental, untrusted certificate minimizer. It uses the existing C++
// checker as a search oracle; that is not an independent validation of this
// transformation. Generated candidates must still pass Lean's unchanged checker.
// Keep the standalone checker source unchanged and retain its original CLI.
#define main five_colour_certificate_checker_main
#include "check_five_colour_certificate.cpp"
#undef main

#include <chrono>
#include <filesystem>
#include <stdexcept>

struct Node {
    int op, reason, value=0, left=-1, right=-1;
};

struct Minimizer : Checker {
    std::vector<Node> nodes;
    unsigned long long trials=0, visits=0, exhausted=0;
    int trial_limit;
    explicit Minimizer(int limit):trial_limit(limit) {}

    void parse() {
        struct Pending {int parent, side;};
        std::vector<Pending> pending{{-1,0}};
        position=160;
        while(!pending.empty()) {
            auto link=pending.back();pending.pop_back();
            Node node{byte(),byte()};
            if(node.op==1)node.value=byte();
            int id=nodes.size();nodes.push_back(node);
            if(link.parent>=0)
                (link.side?nodes[link.parent].right:nodes[link.parent].left)=id;
            if(node.op==1)pending.push_back({id,1});
            if(node.op!=0)pending.push_back({id,0});
        }
        if(position!=data.size())throw std::runtime_error("trailing input data");
    }

    // A budget exhausted trial is simply unsuccessful; it never establishes
    // an exclusion. The final candidate is replayed without a trial budget.
    bool verify(int id,Box box,int &fuel) {
        while(true) {
            if(fuel--<=0){++exhausted;return false;}
            ++visits;auto node=nodes[id];
            if(node.op==0)return excluded(box,node.reason);
            if(node.op==2) {
                if(!refine(box,node.reason))return false;
                id=node.left;continue;
            }
            int i=node.reason,v=node.value;
            if(v<box.lower[i]||v>=box.upper[i])return false;
            Box left=box;left.upper[i]=v;box.lower[i]=v+1;
            return verify(node.left,left,fuel)&&verify(node.right,box,fuel);
        }
    }

    bool trial(int id,const Box &box) {
        ++trials;int fuel=trial_limit;return verify(id,box,fuel);
    }

    int minimize(int id,Box box) {
        auto node=nodes[id];
        if(node.op==0)return id;
        // Dropping a refinement or split is permitted only when one complete
        // remaining subtree excludes the larger, unrefined parent box.
        if(trial(node.left,box))return minimize(node.left,box);
        if(node.op==2) {
            if(!refine(box,node.reason))throw std::runtime_error("invalid refinement");
            nodes[id].left=minimize(node.left,box);return id;
        }
        if(trial(node.right,box))return minimize(node.right,box);
        Box left=box;left.upper[node.reason]=node.value;
        box.lower[node.reason]=node.value+1;
        nodes[id].left=minimize(node.left,left);
        nodes[id].right=minimize(node.right,box);
        return id;
    }

    void emit(int root,std::ostream &out) const {
        out.write(reinterpret_cast<const char*>(data.data()),160);
        std::vector<int> pending{root};
        while(!pending.empty()) {
            auto node=nodes[pending.back()];pending.pop_back();
            out.put(node.op);out.put(node.reason);
            if(node.op==1){out.put(node.value);pending.push_back(node.right);}
            if(node.op!=0)pending.push_back(node.left);
        }
    }
};

int main(int argc,char **argv) {
    try {
        if(argc!=6&&argc!=7)
            throw std::runtime_error("GEOMETRY CASES INPUT CASE OUTPUT [TRIAL_LIMIT=4096]");
        if(std::filesystem::weakly_canonical(argv[3])==std::filesystem::weakly_canonical(argv[5]))
            throw std::runtime_error("input and output must differ");
        int selected=std::stoi(argv[4]),limit=argc==7?std::stoi(argv[6]):4096;
        if(limit<1)throw std::runtime_error("trial limit must be positive");
        std::ifstream geometry(argv[1]);int size,x;
        if(!(geometry>>size)||size!=n)throw std::runtime_error("bad geometry size");
        for(int j=0;j<n*6;++j)
            if(!(geometry>>x)||x<0||x>=5)throw std::runtime_error("bad face data");
        for(int t=0;t<n;++t)for(int i=0;i<n;++i) {
            if(!(geometry>>x)||x<0||x>255)throw std::runtime_error("bad incidence data");
            for(int d=1;d<256;++d)if(x&d)
                (i<64?neighbours[t][d].a:neighbours[t][d].b)|=uint64_t(1)<<(i%64);
        }
        std::ifstream cases(argv[2]);int count;
        if(!(cases>>count)||selected<0||selected>=count)throw std::runtime_error("bad case index");
        std::array<int,156> row;
        for(int i=0;i<=selected;++i)for(int &v:row)
            if(!(cases>>v))throw std::runtime_error("truncated cases");
        Minimizer optimizer(limit);
        if(!optimizer.run(argv[3],row))throw std::runtime_error("input certificate rejected");
        auto before=optimizer.commands;
        optimizer.parse();
        Box root;
        for(int i=0;i<n;++i)root.upper[i]=row[6+i];
        root.lower[row[4]]=root.upper[row[4]]=row[1];
        auto start=std::chrono::steady_clock::now();
        int result=optimizer.minimize(0,root);
        {
            std::ofstream out(argv[5],std::ios::binary);
            if(!out)throw std::runtime_error("cannot create output");
            optimizer.emit(result,out);
            if(!out)throw std::runtime_error("cannot write output");
        }
        Checker check;
        if(!check.run(argv[5],row))throw std::runtime_error("candidate certificate rejected");
        double seconds=std::chrono::duration<double>(std::chrono::steady_clock::now()-start).count();
        std::cout<<"{\"case\":"<<selected<<",\"before\":"<<before
                 <<",\"after\":"<<check.commands<<",\"trials\":"<<optimizer.trials
                 <<",\"visited\":"<<optimizer.visits<<",\"exhausted\":"<<optimizer.exhausted
                 <<",\"trial_limit\":"<<limit<<",\"seconds\":"<<seconds<<"}\n";
    } catch(const std::exception &error) {
        std::cerr<<error.what()<<'\n';return 1;
    }
}
