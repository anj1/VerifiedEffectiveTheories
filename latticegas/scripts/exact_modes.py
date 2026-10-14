#!/usr/bin/env python3
"""Exact Q(sqrt(3)) Fourier-power intervals for L=12 axis modes 1..3."""
import json, math, pathlib
from fractions import Fraction
import numpy as np
import research
ROOT=pathlib.Path(__file__).resolve().parent
# 2 exp(-2 pi i n/12) = A + B sqrt(3) + i(C + D sqrt(3)).
PHASE=[(2,0,0,0),(0,1,-1,0),(1,0,0,-1),(0,0,-2,0),
       (-1,0,0,-1),(0,-1,-1,0),(-2,0,0,0),(0,-1,1,0),
       (-1,0,0,1),(0,0,2,0),(1,0,0,1),(0,1,1,0)]
scale=10**40
lower_sqrt=math.isqrt(3*scale*scale)
assert lower_sqrt**2<=3*scale*scale<(lower_sqrt+1)**2
rlo=Fraction(lower_sqrt,scale);rhi=Fraction(lower_sqrt+1,scale)
def interval(K,M,den):
    base=Fraction(K,den)
    x=Fraction(M,den)
    return (base+x*(rlo if M>=0 else rhi),
            base+x*(rhi if M>=0 else rlo))
def dec(q):
    return format(float(q),'.16g')
def rational(q):
    return f"{q.numerator}/{q.denominator}"
files=sorted((ROOT/"data"/"raw").glob("L12_*_G*_B*_S*.jsonl"))
out=[]
for path in files:
    rows=research.read(path);R=len(rows);N=rows[0]["N"]
    _,fft_values=research.spectrum(rows)
    modes=[]
    for m in [1,2,3]:
        totalK=0;totalM=0
        for row in rows:
            s=np.fromiter((int(c) for c in row["bits"]),dtype=np.int64).reshape((12,12,12))
            for axis in range(3):
                counts=s.sum(axis=tuple(i for i in range(3) if i!=axis))
                A=B=C=D=0
                for n,count in enumerate(counts):
                    aa,bb,cc,dd=PHASE[(m*n)%12]
                    A+=int(count)*aa;B+=int(count)*bb
                    C+=int(count)*cc;D+=int(count)*dd
                totalK+=A*A+C*C+3*(B*B+D*D)
                totalM+=2*(A*B+C*D)
        lo,hi=interval(totalK,totalM,12*N*R)
        assert abs((float(lo)+float(hi))/2-float(fft_values[:,m-1].mean()))<1e-10
        modes.append({"mode":m,"K":totalK,"M":totalM,"denominator":12*N*R,
                      "lower":dec(lo),"upper":dec(hi),
                      "lower_fraction":rational(lo),"upper_fraction":rational(hi),
                      "interval_width":format(float(hi-lo),'.3e')})
    out.append({"path":str(path.relative_to(ROOT)),"sha256":research.sha(path),
                "q":[rows[0]["q_num"],rows[0]["q_den"]],
                "initial":rows[0]["initial"],"global_sweeps":rows[0]["aux_global_sweeps"],
                "local_sweeps":rows[0]["burn_sweeps"],"R":R,"modes":modes})
def find(q,initial,G):
    return next(v for v in out if v["q"]==q and v["initial"]==initial and v["global_sweeps"]==G)
def bounds(v):
    x=v["modes"][0];return interval(x["K"],x["M"],x["denominator"])
far=find([4,5],"random",1000);near=find([3,7],"random",1000)
assert (far["modes"][0]["K"],far["modes"][0]["M"],far["modes"][0]["denominator"]) == (418188,44744,663552)
assert (near["modes"][0]["K"],near["modes"][0]["M"],near["modes"][0]["denominator"]) == (2440980,1203140,663552)
flo,fhi=bounds(far);nlo,nhi=bounds(near)
assert flo>0
ratio=(nlo/fhi,nhi/flo)
certificate={"field":"Q(sqrt(3))","L":12,"modes":[1,2,3],
  "sqrt3_scaled_lower":str(lower_sqrt),"sqrt3_scale":str(scale),
  "sqrt3_integer_certificate":[str(lower_sqrt**2),str(3*scale*scale),str((lower_sqrt+1)**2)],
  "rounding":"Exact integer Fourier sums; rational sqrt(3) bracketing",
  "datasets":out,"near_far_ratio_interval":[dec(ratio[0]),dec(ratio[1])],
  "near_far_ratio_interval_fractions":[rational(ratio[0]),rational(ratio[1])],
  "scope":"Exact arithmetic conditional on the recorded bits; bit extraction is external Python."}
p=ROOT/"results"/"exact_spectrum_intervals.json"
p.write_text(json.dumps(certificate,indent=2)+"\n")
print(json.dumps({"datasets":len(out),"near_far_ratio_interval":certificate["near_far_ratio_interval"],
  "max_width":max(float(m["interval_width"]) for x in out for m in x["modes"])}))
