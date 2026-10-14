// Exact rational Metropolis acceptance; deterministic SplitMix64 bit stream.
// Compile: g++ -O3 -std=c++17 simulator.cpp -o simulator
#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>
using u64 = std::uint64_t;
struct Rng {
  u64 state;
  u64 next() {
    state += 0x9e3779b97f4a7c15ULL;
    u64 z = state;
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
  }
  u64 bounded(u64 m) {
    if (!m) throw std::runtime_error("zero range");
    const u64 threshold = (u64(0) - m) % m;
    for (;;) { u64 x = next(); if (x >= threshold) return x % m; }
  }
};
int main(int argc, char **argv) {
  if (argc != 10 && argc != 11) {
    std::cerr << "usage: simulator L q_num q_den replicas local_sweeps seed initial out.jsonl check_every [aux_global_sweeps]\n";
    return 2;
  }
  const int L = std::stoi(argv[1]), a = std::stoi(argv[2]), d = std::stoi(argv[3]);
  const int reps = std::stoi(argv[4]), burn = std::stoi(argv[5]);
  const u64 seed = std::stoull(argv[6]);
  const std::string initial = argv[7], out = argv[8];
  const int check_every = std::stoi(argv[9]);
  const int aux_global = argc == 11 ? std::stoi(argv[10]) : 0;
  if (L < 2 || u64(L)*u64(L)*u64(L) > u64(std::numeric_limits<int>::max()/3) ||
      a <= 0 || d <= a || reps < 1 || burn < 0 || aux_global < 0 || check_every < 0 ||
      (initial != "random" && initial != "slab")) return 2;
  const int V=L*L*L, N=V/2;
  auto index = [L](int x,int y,int z) { return (x*L+y)*L+z; };
  auto coords = [L](int i,int &x,int &y,int &z) { z=i%L; y=(i/L)%L; x=i/(L*L); };
  auto neighbor = [&](int i,int axis,int step) {
    int x,y,z; coords(i,x,y,z);
    if(axis==0) x=(x+step+L)%L;
    if(axis==1) y=(y+step+L)%L;
    if(axis==2) z=(z+step+L)%L;
    return index(x,y,z);
  };
  auto contact_total = [&](const std::vector<std::uint8_t>& state) {
    int total=0;
    for(int k=0;k<V;k++) for(int c=0;c<3;c++)
      total+=state[k]*state[neighbor(k,c,1)];
    return total;
  };
  std::ofstream file(out);
  if(!file) throw std::runtime_error("cannot open output");
  for(int r=0;r<reps;r++) {
    // Each replica uses a separately seeded stream.  This is a deterministic
    // reproducibility device, not a proof of probabilistic independence.
    Rng rng{seed + 0x9e3779b97f4a7c15ULL*u64(r+1)};
    std::vector<std::uint8_t> s(V,0);
    if(initial=="random") {
      std::vector<int> order(V);
      for(int i=0;i<V;i++) order[i]=i;
      for(int i=V-1;i>0;i--) std::swap(order[i],order[rng.bounded(i+1)]);
      for(int i=0;i<N;i++) s[order[i]]=1;
    } else {
      for(int i=0;i<N;i++) s[i]=1;
    }
    u64 accepted=0, uphill=0, aux_accepted=0;
    auto attempt = [&](int i,int j,u64 step,u64 &counter) {
      if(s[i]==s[j]) return;
      int ni=0,nj=0;
      for(int c=0;c<3;c++) for(int dir : {-1,1}) {
        int vi=neighbor(i,c,dir), vj=neighbor(j,c,dir);
        if(vi!=j) ni+=s[vi];
        if(vj!=i) nj+=s[vj];
      }
      int de=(int(s[i])-int(s[j]))*(ni-nj); // H_after - H_before in units J
      if(check_every && step%u64(check_every)==0) {
        int before=contact_total(s);
        std::swap(s[i],s[j]);
        int after=contact_total(s);
        std::swap(s[i],s[j]);
        if(before-after!=de) throw std::runtime_error("local energy mismatch");
      }
      bool take=true;
      if(de>0) {
        uphill++;
        u64 numerator=1,denominator=1;
        for(int k=0;k<de;k++) {
          if(numerator>std::numeric_limits<u64>::max()/u64(a) ||
             denominator>std::numeric_limits<u64>::max()/u64(d))
            throw std::runtime_error("rational acceptance overflow");
          numerator*=u64(a); denominator*=u64(d);
        }
        take=rng.bounded(denominator)<numerator;
      }
      if(take) {std::swap(s[i],s[j]);counter++;}
      if(check_every && step%u64(check_every)==0) {
        int count=0;for(auto v:s) count+=v;
        if(count!=N) throw std::runtime_error("particle count changed");
      }
    };
    for(u64 step=0;step<u64(aux_global)*V;step++) {
      int i=int(rng.bounded(V)),j=int(rng.bounded(V));
      attempt(i,j,step,aux_accepted);
    }
    for(u64 step=0;step<u64(burn)*V;step++) {
      int b=int(rng.bounded(u64(3)*V)), i=b/3, axis=b%3;
      attempt(i,neighbor(i,axis,1),step,accepted);
    }
    int contacts=contact_total(s);
    file << "{\"version\":\"rational-kawasaki-v2\",\"L\":"<<L
      <<",\"N\":"<<N<<",\"q_num\":"<<a<<",\"q_den\":"<<d
      <<",\"burn_sweeps\":"<<burn<<",\"aux_global_sweeps\":"<<aux_global
      <<",\"aux_accepted\":"<<aux_accepted<<",\"replica\":"<<r
      <<",\"master_seed\":"<<seed<<",\"replica_seed\":"
      <<(seed+0x9e3779b97f4a7c15ULL*u64(r+1))
      <<",\"initial\":\""<<initial<<"\",\"accepted\":"<<accepted
      <<",\"uphill_proposed\":"<<uphill<<",\"contacts\":"<<contacts
      <<",\"bits\":\"";
    for(auto v:s) file << char('0'+v);
    file << "\"}\n";
  }
}
