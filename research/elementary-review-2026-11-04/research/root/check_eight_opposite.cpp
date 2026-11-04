// Independent small audit of the elementary eight-opposite theorem.
// Constructs all fifteen K5 four-cycles without loading generated data.
#include <array>
#include <bit>
#include <cstdint>
#include <iostream>
#include <vector>

using namespace std;
array<uint16_t,15> cycle{};
array<array<uint16_t,16>,15> neighbours{};
array<int,15> count{};
array<long long,5> profiles{};
long long checked=0, failures=0;

int edge(int a,int b) {
    if(a>b) swap(a,b);
    int k=0;
    for(int i=0;i<5;i++) for(int j=i+1;j<5;j++,k++)
        if(a==i && b==j) return k;
    return -1;
}

void inspect() {
    checked++;
    int doubled=0;
    for(int n:count) doubled+=(n==2);
    profiles[doubled]++;
    for(int t=0;t<15;t++) {
        bool good=true;
        for(int s=1;s<16;s++) {
            int available=0;
            for(int j=0;j<15;j++) if(neighbours[t][s]>>j&1)
                available+=count[j];
            if(available<2*popcount(unsigned(s))) { good=false; break; }
        }
        if(good) return;
    }
    failures++;
    if(failures<=5) {
        cerr << "Failure:";
        for(int n:count) cerr << ' ' << n;
        cerr << '\n';
    }
}

void allocate(int j,int left) {
    if(j==15) { if(left==0) inspect(); return; }
    if(left>2*(15-j)) return;
    for(int n=0;n<=2 && n<=left;n++) {
        count[j]=n;
        allocate(j+1,left-n);
    }
    count[j]=0;
}

int main() {
    int k=0;
    for(int omitted=0;omitted<5;omitted++) {
        vector<int> v;
        for(int i=0;i<5;i++) if(i!=omitted) v.push_back(i);
        for(int second=1;second<4;second++) {
            uint16_t m=0;
            for(int a:{v[0],v[second]}) for(int b:v)
                if(b!=v[0] && b!=v[second]) m|=1u<<edge(a,b);
            cycle[k++]=m;
        }
    }
    for(int t=0;t<15;t++) {
        vector<int> edges;
        for(int e=0;e<10;e++) if(cycle[t]>>e&1) edges.push_back(e);
        for(int s=1;s<16;s++) {
            uint16_t m=0;
            for(int e=0;e<4;e++) if(s>>e&1) m|=1u<<edges[e];
            for(int j=0;j<15;j++) if(cycle[j]&m) neighbours[t][s]|=1u<<j;
        }
    }
    allocate(0,8);
    cout << "Inventories " << checked << "; failures " << failures << '\n';
    for(int d=0;d<5;d++)
        cout << d << " doubled varieties: " << profiles[d] << '\n';
    return failures ? 1 : 0;
}
