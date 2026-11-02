// Untrusted Q5P2-to-Lean chunk exporter. Lean checks every emitted boundary
// and composes already proved exclusions; this program is not in the trust base.
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
    std::ostream &out;
    explicit Exporter(std::ostream &stream):out(stream){}
    int byte(){if(position>=data.size())throw std::runtime_error("truncated tree");return data[position++];}
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
                if(node.a>76)throw std::runtime_error("invalid reason");
                // No mass-refinement instruction occurs in the current archive.
                if(node.op==2&&node.a==0)throw std::runtime_error("mass refinement not supported");
            } else throw std::runtime_error("invalid opcode");
            nodes.push_back(node);
            if(link.parent>=0)(link.side?nodes[link.parent].right:nodes[link.parent].left)=id;
            if(node.op==1)pending.push_back({id,1});
            if(node.op!=0)pending.push_back({id,0});
        }
        if(position!=data.size())throw std::runtime_error("trailing bytes");
        for(int i=int(nodes.size())-1;i>=0;--i) {
            if(nodes[i].left>=0)nodes[i].size+=nodes[nodes[i].left].size;
            if(nodes[i].right>=0)nodes[i].size+=nodes[nodes[i].right].size;
        }
        return 0;
    }
    void whole(int id,std::ostream &s) const {
        const auto &v=nodes[id];
        if(v.op==0) {
            if(v.a==0)s<<".mass";else s<<"(.close "<<v.a+1<<')';
        } else if(v.op==2) {
            s<<"(.step "<<v.a+1<<' ';whole(v.left,s);s<<')';
        } else {
            s<<"(.split "<<v.a<<' '<<v.b<<' ';whole(v.left,s);s<<' ';whole(v.right,s);s<<')';
        }
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
        if(v.size==residual[id]) {
            s<<"(.run ";whole(id,s);s<<')';return;
        }
        if(v.op==2) {
            if(!refine(box,v.a))throw std::runtime_error("invalid refinement");
            s<<"(.step "<<v.a+1<<' ';render(v.left,box,false,refs,s);s<<')';
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
        if(argc!=7)throw std::runtime_error("GEOMETRY CASES CERTIFICATE CASE LIMIT OUTPUT");
        std::ifstream geometry(argv[1]);int size,x;geometry>>size;
        if(size!=n)throw std::runtime_error("bad geometry size");
        for(int j=0;j<n*6;++j)geometry>>x;
        for(int t=0;t<n;++t)for(int i=0;i<n;++i) {
            geometry>>x;if(x<0||x>255)throw std::runtime_error("bad incidence");
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
        if(e.data.size()<160||std::string(e.data.begin(),e.data.begin()+4)!="Q5P2")
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
        e.parse();e.plan();int last=e.chunk(0,root);
        if(!out)throw std::runtime_error("output failure");
        std::cout<<"case="<<selected<<" commands="<<e.nodes.size()<<" chunks="<<e.chunks<<" root="<<last<<'\n';
    } catch(const std::exception &e) {std::cerr<<e.what()<<'\n';return 1;}
}
