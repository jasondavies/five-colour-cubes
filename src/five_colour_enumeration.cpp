// Q5E1 classification certificate replayer and untrusted Lean chunk exporter. Lean checks every emitted boundary
// and composes already proved coverage statements; this program is not in the trust base.
// The interval formulas mirror the separate C++ replay checker.
#include <algorithm>
#include <array>
#include <bit>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <iterator>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>
#include <set>
constexpr int n=75;
using Vector=std::array<int,n>;
struct Box {Vector lower{},upper{};};
struct Mask {uint64_t a=0,b=0;};
std::array<std::array<Mask,256>,n> neighbours;
std::string bound_digits(const Vector &v) {
    std::string result;
    for(int value:v) {
        if(value<0||value>7)throw std::runtime_error("out-of-range bound");
        result+=char('0'+value);
    }
    return result;
}
struct Node {int op=0,a=0,b=0,left=-1,right=-1,size=1;};
struct Exporter {
    std::vector<unsigned char> data;
    size_t position=160;
    std::vector<Node> nodes;
    std::vector<int> residual;
    std::vector<bool> boundary;
    int goal=0,budget=0,limit=0,chunks=0;
    Vector bad{};
    struct LocalCut { Mask mask; int rhs; };
    std::array<std::vector<LocalCut>,78> families;
    std::set<Vector> allowed, observed;
    std::ostream &out;
    explicit Exporter(std::ostream &stream):out(stream){}
    int byte(){if(position>=data.size())throw std::runtime_error("truncated tree");return data[position++];}
    bool refine(Box &box,int reason) {
        if(reason<0||reason>=78)throw std::runtime_error("bad family");
        int upper=0; for(int h:box.upper)upper+=h;
        Mask common{~uint64_t(0),~uint64_t(0)},united{};
        int slack=-1,need=1000;
        for(auto cut:families[reason]) {
            int il=0,iu=0;
            for(int i=0;i<n;++i)if((i<64?cut.mask.a:cut.mask.b)&(uint64_t(1)<<(i%64))) {
                il+=box.lower[i];iu+=box.upper[i];
            }
            int ou=upper-iu;
            if(il>cut.rhs||ou+cut.rhs<goal)continue;
            common.a&=cut.mask.a;common.b&=cut.mask.b;
            united.a|=cut.mask.a;united.b|=cut.mask.b;
            slack=std::max(slack,cut.rhs-il);need=std::min(need,goal-cut.rhs-ou);
        }
        if(slack<0)return false;
        Box result=box;
        for(int i=0;i<n;++i) {
            uint64_t bit=uint64_t(1)<<(i%64);
            if((i<64?common.a:common.b)&bit)result.upper[i]=std::min(box.upper[i],box.lower[i]+slack);
            if(!((i<64?united.a:united.b)&bit))result.lower[i]=std::max(box.lower[i],box.upper[i]+need);
            if(result.lower[i]>result.upper[i])throw std::runtime_error("bad resulting bound");
        }
        box=result;return true;
    }
    int parse() {
        // Parse prefix syntax with an explicit stack, including long step chains.
        struct Pending {int parent,side;};
        std::vector<Pending> pending{{-1,0}};
        while(!pending.empty()) {
            auto link=pending.back();pending.pop_back();
            int id=nodes.size();Node node;node.op=byte();node.a=byte();
            if(node.op==1) {
                node.b=byte();
                if(node.a>=n||node.b>=7)throw std::runtime_error("invalid split");
            } else if(node.op==0||node.op==2) {
                if(node.a>=78 && !(node.op==0&&node.a==255))throw std::runtime_error("invalid reason");
            } else if(node.op==3) {
                if(node.a!=0)throw std::runtime_error("bad point opcode");
            } else throw std::runtime_error("invalid opcode");
            nodes.push_back(node);
            if(link.parent>=0)(link.side?nodes[link.parent].right:nodes[link.parent].left)=id;
            if(node.op==1)pending.push_back({id,1});
            if(node.op==1||node.op==2)pending.push_back({id,0});
        }
        if(position!=data.size())throw std::runtime_error("trailing bytes");
        for(int i=int(nodes.size())-1;i>=0;--i) {
            if(nodes[i].left>=0)nodes[i].size+=nodes[nodes[i].left].size;
            if(nodes[i].right>=0)nodes[i].size+=nodes[nodes[i].right].size;
        }
        return 0;
    }
    void plan() {
        residual.resize(nodes.size());boundary.assign(nodes.size(),false);
        for(int id=int(nodes.size())-1;id>=0;--id) {
            const auto &v=nodes[id];
            int left=v.left<0?0:residual[v.left],right=v.right<0?0:residual[v.right];
            if(1+left+right>limit) {
                if(left>=right){boundary[v.left]=true;left=0;}
                else {boundary[v.right]=true;right=0;}
            }
            if(1+left+right>limit) {
                if(left){boundary[v.left]=true;left=0;}
                else {boundary[v.right]=true;right=0;}
            }
            residual[id]=1+left+right;
        }
    }
    void render(int id,Box box,bool root,std::vector<int> &refs,std::ostream &s) {
        const auto v=nodes[id];
        if(!root&&boundary[id]) {
            int child=chunk(id,box),slot=refs.size();refs.push_back(child);
            s<<"(.reuse "<<slot<<')';return;
        }
        if(v.op==0) {
            if(v.a==255) {
                int low=0,high=0;for(int i=0;i<n;++i){low+=box.lower[i];high+=box.upper[i];}
                if(low<=goal&&goal<=high)throw std::runtime_error("invalid mass closure");
                s<<"(.run .mass)";
            } else {
                if(refine(box,v.a))throw std::runtime_error("invalid family closure");
                s<<"(.run (.close "<<v.a<<"))";
            }
            return;
        }
        if(v.op==3) {
            if(box.lower!=box.upper||!allowed.contains(box.lower))throw std::runtime_error("unlisted point");
            observed.insert(box.lower);s<<".point";return;
        }
        if(v.op==2) {
            if(!refine(box,v.a))throw std::runtime_error("invalid refinement");
            s<<"(.step "<<v.a<<' ';render(v.left,box,false,refs,s);s<<')';
        } else if(v.op==1) {
            if(v.b<box.lower[v.a]||v.b>=box.upper[v.a])throw std::runtime_error("invalid branch");
            Box left=box;left.upper[v.a]=v.b;box.lower[v.a]=v.b+1;
            s<<"(.split "<<v.a<<' '<<v.b<<' ';
            render(v.left,left,false,refs,s);s<<' ';render(v.right,box,false,refs,s);s<<')';
        } else throw std::runtime_error("unreachable leaf");
    }
    int chunk(int id,const Box &box) {
        std::ostringstream expression;std::vector<int> refs;
        render(id,box,true,refs,expression);
        int index=chunks++;
        out<<index<<'\t'<<bound_digits(box.lower)<<'\t'<<bound_digits(box.upper)<<'\t'<<residual[id]<<'\t';
        for(size_t i=0;i<refs.size();++i){if(i)out<<',';out<<refs[i];}
        out<<'\t'<<expression.str()<<'\n';
        return index;
    }
};
int main(int argc,char **argv) {
    try {
        if(argc!=9)throw std::runtime_error("GEOMETRY CASES CERTIFICATE CASE LIMIT OUTPUT FAMILIES POINTS");
        std::ifstream geometry(argv[1]);int size,x;
        if(!(geometry>>size)||size!=n)throw std::runtime_error("bad geometry size");
        for(int j=0;j<n*6;++j)if(!(geometry>>x)||x<0||x>=5)throw std::runtime_error("bad face data");
        for(int t=0;t<n;++t)for(int i=0;i<n;++i) {
            if(!(geometry>>x)||x<0||x>255)throw std::runtime_error("bad incidence");
            for(int d=1;d<256;++d)if(x&d)
                (i<64?neighbours[t][d].a:neighbours[t][d].b)|=uint64_t(1)<<(i%64);
        }
        if(!geometry)throw std::runtime_error("truncated geometry");
        std::ifstream cases(argv[2]);int count;cases>>count;int selected=std::stoi(argv[4]);
        if(!cases||selected<0||selected>=count)throw std::runtime_error("bad case index");
        std::array<int,156> expected;
        for(int i=0;i<=selected;++i)for(int &v:expected)cases>>v;
        if(!cases)throw std::runtime_error("truncated cases");
        std::ofstream out(argv[6]);if(!out)throw std::runtime_error("cannot open output");
        Exporter e(out);e.limit=std::stoi(argv[5]);
        if(e.limit<1||e.limit>1024)throw std::runtime_error("chunk limit must be 1..1024");
        std::ifstream in(argv[3],std::ios::binary);if(!in)throw std::runtime_error("cannot read certificate");
        e.data.assign(std::istreambuf_iterator<char>(in),{});
        if(e.data.size()<160||std::string(e.data.begin(),e.data.begin()+4)!="Q5E1")
            throw std::runtime_error("bad header");
        for(size_t i=0;i<expected.size();++i)if(e.data[i+4]!=expected[i])throw std::runtime_error("case mismatch");
        e.goal=expected[3];e.budget=expected[5];Box root;
        for(int i=0;i<n;++i) {
            root.upper[i]=expected[6+i];e.bad[i]=expected[81+i];
            if(root.upper[i]<0||root.upper[i]>7||e.bad[i]<0||e.bad[i]>1)
                throw std::runtime_error("invalid root bounds or budget mask");
        }
        if(e.goal<0||e.budget<0||e.budget>7)throw std::runtime_error("bad goal or budget");
        int anchor=expected[4],m=expected[1];
        if(anchor<0||anchor>=n||m<1||m>7)throw std::runtime_error("bad anchor");
        root.lower[anchor]=root.upper[anchor]=m;
        e.families[0].push_back({{},0});
        e.families[1].push_back({{~uint64_t(0),(uint64_t(1)<<11)-1},e.goal});
        Mask badmask{};for(int i=0;i<n;++i)if(e.bad[i])(i<64?badmask.a:badmask.b)|=uint64_t(1)<<(i%64);
        e.families[2].push_back({badmask,e.budget});
        std::ifstream familyfile(argv[7]);
        for(int t=0;t<n;++t) {
            int count; if(!(familyfile>>count)||count<0||count>255)throw std::runtime_error("bad family count");
            for(int j=0;j<count;++j) {
                Exporter::LocalCut cut;
                if(!(familyfile>>cut.mask.a>>cut.mask.b>>cut.rhs)||cut.rhs<0||cut.rhs>7||cut.mask.b>=2048)throw std::runtime_error("bad local cut");
                e.families[t+3].push_back(cut);
            }
        }
        std::ifstream points(argv[8]);
        if(!(points>>count)||count<0)throw std::runtime_error("bad points count");
        for(int j=0;j<count;++j) {
            Vector point;for(int &v:point)if(!(points>>v)||v<0||v>7)throw std::runtime_error("bad point");
            e.allowed.insert(point);
        }
        // Check that each original Hall alternative possible in the root
        // implies one supplied reduced alternative. No search result is used.
        int rootupper=0; for(int h:root.upper)rootupper+=h;
        for(int t=0;t<n;++t)for(unsigned subset=1;subset<256;++subset) {
            Mask c=neighbours[t][subset];int rhs=std::popcount(subset)-1,cl=0,cu=0;
            for(int i=0;i<n;++i)if((i<64?c.a:c.b)&(uint64_t(1)<<(i%64))) {
                cl+=root.lower[i];cu+=root.upper[i];
            }
            if(cl>rhs||rootupper-cu+rhs<e.goal)continue;
            bool covered=false;
            for(auto d:e.families[t+3]) {
                if((d.mask.a&c.a)!=d.mask.a||(d.mask.b&c.b)!=d.mask.b)continue;
                int dl=0;for(int i=0;i<n;++i)if((i<64?d.mask.a:d.mask.b)&(uint64_t(1)<<(i%64)))dl+=root.lower[i];
                if(rhs+dl<=d.rhs+cl){covered=true;break;}
            }
            if(!covered)throw std::runtime_error("uncovered original Hall alternative");
        }
        e.parse();e.plan();int last=e.chunk(0,root);
        if(!out)throw std::runtime_error("output failure");
        if(e.observed!=e.allowed)throw std::runtime_error("terminal point set differs");
        std::cout<<"case="<<selected<<" commands="<<e.nodes.size()<<" chunks="<<e.chunks<<" root="<<last<<'\n';
    } catch(const std::exception &e) {std::cerr<<e.what()<<'\n';return 1;}
}
