// Separate grand-canonical zero-field Ising experiment. C++20, no external libraries.
// The finite-volume target is pi_r(s) proportional to r^D(s).
// The PRNG is reproducible, but exact-distribution claims are conditional on ideal
// independent unbiased random words. CFTP uses exact rational thresholds.
#include <algorithm>
#include <array>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

using u64 = std::uint64_t;
using u128 = __uint128_t;

struct RNG {
  u64 state;
  explicit RNG(u64 seed) : state(seed) {}
  static u64 mix(u64 z) {
    z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9ULL;
    z = (z ^ (z >> 27)) * 0x94d049bb133111ebULL;
    return z ^ (z >> 31);
  }
  u64 word() {
    state += 0x9e3779b97f4a7c15ULL;
    return mix(state);
  }
  u64 below(u64 n) {
    if (!n) throw std::runtime_error("zero random bound");
    const u64 threshold = -n % n;
    while (true) {
      u64 x = word();
      if (x >= threshold) return x % n;
    }
  }
};

u64 ipow(u64 b, int p) {
  u64 x = 1;
  for (int i = 0; i < p; ++i) {
    if (b && x > std::numeric_limits<u64>::max() / b) throw std::runtime_error("power overflow");
    x *= b;
  }
  return x;
}

u64 checked_mul(u64 x,u64 y) {
  if(y && x>std::numeric_limits<u64>::max()/y)throw std::runtime_error("integer overflow");
  return x*y;
}

struct Lattice {
  int L, V;
  std::vector<std::array<int, 6>> nbr;
  std::vector<std::pair<int, int>> edge;
  explicit Lattice(int side) : L(side), V(side * side * side), nbr(V) {
    if (L < 2 || L > 128) throw std::runtime_error("require 2 <= L <= 128");
    for (int z = 0; z < L; ++z) for (int y = 0; y < L; ++y) for (int x = 0; x < L; ++x) {
      int i = idx(x,y,z);
      nbr[i] = {idx((x+1)%L,y,z),idx((x+L-1)%L,y,z),
                idx(x,(y+1)%L,z),idx(x,(y+L-1)%L,z),
                idx(x,y,(z+1)%L),idx(x,y,(z+L-1)%L)};
      edge.push_back({i,nbr[i][0]});
      edge.push_back({i,nbr[i][2]});
      edge.push_back({i,nbr[i][4]});
    }
  }
  int idx(int x,int y,int z) const { return x + L*(y+L*z); }
};

struct RationalHeat {
  u64 a,b,M;
  std::array<u64,7> numerator{}, denominator{};
  RationalHeat(u64 an,u64 bn) : a(an),b(bn),M(1) {
    if (!a || a>=b) throw std::runtime_error("require 0 < r numerator < denominator");
    for (int k=0;k<=6;++k) {
      u64 n=checked_mul(ipow(a,6-k),ipow(b,k));
      u64 t=checked_mul(ipow(a,k),ipow(b,6-k));
      if (std::numeric_limits<u64>::max()-n < t) throw std::runtime_error("probability overflow");
      u64 d=n+t, g=std::gcd(n,d);
      numerator[k]=n/g; denominator[k]=d/g;
      u64 reduced=denominator[k]/std::gcd(M,denominator[k]);
      if (M>std::numeric_limits<u64>::max()/reduced) throw std::runtime_error("common rational denominator overflow");
      M*=reduced;
    }
    for (int k=1;k<=6;++k)
      if ((u128)numerator[k-1]*denominator[k] > (u128)numerator[k]*denominator[k-1])
        throw std::runtime_error("heat-bath probability is not monotone");
  }
  bool plus(int k,u64 u) const {
    return (u128)u*denominator[k] < (u128)M*numerator[k];
  }
};

struct Instruction { std::uint32_t site; u64 u; };

void heat_update(const Lattice &lat,const RationalHeat &h,std::vector<std::uint8_t> &s,const Instruction &ins) {
  int a=0;
  for (int j : lat.nbr[ins.site]) a += s[j];
  s[ins.site]=h.plus(a,ins.u);
}

u64 fnv(const std::vector<std::uint8_t> &s) {
  u64 h=14695981039346656037ULL;
  for (auto x:s) {h^=x;h*=1099511628211ULL;}
  return h;
}

std::string decimal(u128 v) {
  if(!v)return "0";
  std::string s;
  while(v) {s.push_back(char('0'+v%10));v/=10;}
  std::reverse(s.begin(),s.end());
  return s;
}

void observables(const Lattice &lat,const std::vector<std::uint8_t> &s,std::ostream &out) {
  long long m=0;
  std::uint64_t disagreements=0;
  for (auto [x,y]:lat.edge) disagreements += (s[x]!=s[y]);
  std::array<double,3> re{},im{};
  std::array<std::vector<int>,3> planes;
  for(auto &axis:planes)axis.assign(lat.L,0);
  const double twopi=2.0*std::acos(-1.0);
  for (int z=0;z<lat.L;++z) for (int y=0;y<lat.L;++y) for (int x=0;x<lat.L;++x) {
    int spin=2*int(s[lat.idx(x,y,z)])-1; m+=spin;
    int xyz[]={x,y,z};
    for (int d=0;d<3;++d) {
      planes[d][xyz[d]]+=spin;
      double angle=twopi*xyz[d]/lat.L;
      re[d]+=spin*std::cos(angle); im[d]-=spin*std::sin(angle);
    }
  }
  u128 m2=(u128)(m*m);
  out<<"\"disagreement_count\":"<<disagreements
     <<",\"magnetization_sum\":"<<m<<",\"magnetization_sum_2\":"<<decimal(m2)
     <<",\"magnetization_sum_4\":"<<decimal(m2*m2)<<",\"s0_numerator\":"<<decimal(m2)
     <<",\"sk_axis_numerators\":[";
  for (int d=0;d<3;++d) {if(d)out<<",";out<<std::setprecision(17)<<(re[d]*re[d]+im[d]*im[d]);}
  out<<"]";
#ifndef PRG_LEGACY_V3
  out<<",\"plane_spin_sums\":[";
  for(int d=0;d<3;++d){
    if(d)out<<",";
    out<<"[";
    for(int j=0;j<lat.L;++j){if(j)out<<",";out<<planes[d][j];}
    out<<"]";
  }
  out<<"]";
#endif
}

struct DSU {
  std::vector<int> parent,rank;
  explicit DSU(int n):parent(n),rank(n,0) {std::iota(parent.begin(),parent.end(),0);}
  int find(int x) {while(parent[x]!=x){parent[x]=parent[parent[x]];x=parent[x];}return x;}
  void unite(int x,int y) {x=find(x);y=find(y);if(x==y)return;if(rank[x]<rank[y])std::swap(x,y);parent[y]=x;if(rank[x]==rank[y])++rank[x];}
};

void sw_sweep(const Lattice &lat,const RationalHeat &h,RNG &rng,std::vector<std::uint8_t> &s) {
  DSU d(lat.V);
  for (auto [x,y]:lat.edge)
    if (s[x]==s[y] && rng.below(h.b) < h.b-h.a) d.unite(x,y);
  std::vector<std::int8_t> cluster(lat.V,-1);
  for(int x=0;x<lat.V;++x) {
    int root=d.find(x);
    if(cluster[root]<0)cluster[root]=rng.below(2);
    s[x]=cluster[root];
  }
}

void save_stream(const std::string &path,const std::vector<Instruction> &stream) {
  std::ofstream f(path,std::ios::binary);
  if(!f)throw std::runtime_error("cannot open CFTP stream");
  for(const auto &ins:stream) {f.write(reinterpret_cast<const char*>(&ins.site),4);f.write(reinterpret_cast<const char*>(&ins.u),8);}
  if(!f)throw std::runtime_error("cannot write CFTP stream");
}

int main(int argc,char **argv) {
  try {
    if(argc!=10 && argc!=11)throw std::runtime_error("usage: grandcanonical MODE L R_NUM R_DEN REPLICAS SEED PARAM1 PARAM2 OUTPUT_JSONL [START_REPLICA] (MODE=sw: sweeps,interval; cftp: max_updates,save_streams[0/1])");
    std::string mode=argv[1],output=argv[9];
    Lattice lat(std::stoi(argv[2]));
    RationalHeat h(std::stoull(argv[3]),std::stoull(argv[4]));
    int replicas=std::stoi(argv[5]); u64 seed=std::stoull(argv[6]);
    u64 param1=std::stoull(argv[7]); int param2=std::stoi(argv[8]);
    int start_replica=argc==11?std::stoi(argv[10]):0;
    if(replicas<1)throw std::runtime_error("replicas must be positive");
    if(start_replica<0 || start_replica>std::numeric_limits<int>::max()-replicas)
      throw std::runtime_error("invalid replica range");
    std::ofstream out(output,start_replica?std::ios::app:std::ios::out);
    if(!out)throw std::runtime_error("cannot open output JSONL");
    for(int rep=start_replica;rep<start_replica+replicas;++rep) {
      // Hash the replica identifier. An arithmetic seed progression would make
      // neighbouring replicas overlapping suffixes of one SplitMix64 stream.
      u64 repseed=RNG::mix(seed ^ (0x9e3779b97f4a7c15ULL*u64(rep+1)));
      RNG rng(repseed);
      std::vector<std::uint8_t> s(lat.V);
      u64 horizon=0; bool success=true;
      std::string stream_path="";
      if(mode=="sw") {
        // Each replica has an independent seed, with one observation per chain.
        for(int x=0;x<lat.V;++x)s[x]=rng.below(2);
        for(u64 t=0;t<param1;++t)sw_sweep(lat,h,rng,s);
        for(int t=0;t<param2;++t)sw_sweep(lat,h,rng,s);
      } else if(mode=="cftp") {
        // Prefix extension preserves the random instructions in the old suffix.
        // Never use the successful subset when any replica is censored.
        std::vector<Instruction> stream;
        u64 old=0, target=1;
        while(true) {
          if(target>param1) {success=false;break;}
          std::vector<Instruction> prefix;
          prefix.reserve(target-old);
          for(u64 j=old;j<target;++j)prefix.push_back({(std::uint32_t)rng.below(lat.V),rng.below(h.M)});
          stream.insert(stream.begin(),prefix.begin(),prefix.end());
          std::vector<std::uint8_t> lo(lat.V,0),hi(lat.V,1);
          for(const auto &ins:stream) {heat_update(lat,h,lo,ins);heat_update(lat,h,hi,ins);}
          horizon=target;
          if(lo==hi) {s=std::move(lo);break;}
          old=target;
          if(target>param1/2) {success=false;break;}
          target*=2;
        }
        if(param2) {
          stream_path=output+".rep"+std::to_string(rep)+".bin";
          save_stream(stream_path,stream);
        }
      } else throw std::runtime_error("mode must be sw or cftp");
#ifdef PRG_LEGACY_V3
      out<<"{\"model_version\":\"grandcanonical-v3-prg\",\"ensemble\":\"zero_field_ising\",\"algorithm\":\""<<mode
#else
      out<<"{\"model_version\":\"grandcanonical-v4-prg\",\"ensemble\":\"zero_field_ising\",\"algorithm\":\""<<mode
#endif
         <<"\",\"L\":"<<lat.L<<",\"volume\":"<<lat.V<<",\"r_num\":"<<h.a<<",\"r_den\":"<<h.b
         <<",\"rational_uniform_denominator\":"<<h.M<<",\"replica\":"<<rep<<",\"seed\":"<<repseed
         <<",\"initial_condition\":\""<<(mode=="sw"?"independent_random":"all_minus_all_plus")
         <<"\",\"success\":"<<(success?"true":"false")<<",\"horizon_updates\":"<<horizon
         <<",\"sw_initial_sweeps\":"<<(mode=="sw"?param1:0)<<",\"sw_extra_sweeps\":"<<(mode=="sw"?param2:0)
         <<",\"stream_path\":\""<<stream_path<<"\",\"state_fnv64\":"<<fnv(s);
      if(success){out<<",";observables(lat,s,out);}
      out<<"}\n";
    }
  } catch(const std::exception &e) {std::cerr<<e.what()<<"\n";return 1;}
}
