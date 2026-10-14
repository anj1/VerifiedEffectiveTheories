#!/usr/bin/env python3
"""Derived, explicitly exploratory results and self-contained SVG figures."""
import json, math, pathlib
import numpy as np
import research
ROOT=pathlib.Path(__file__).resolve().parent
OUT=ROOT/"results"; PLOTS=OUT/"plots";PLOTS.mkdir(parents=True,exist_ok=True)
def load(name):
    z=json.loads((OUT/name).read_text())
    return z["data"] if isinstance(z,dict) and "data" in z else z
aux=load("aux_more.json")+load("aux_equilibration.json")+load("aux_scaling.json")
random_rows=sorted((r for r in aux if r["initial"]=="random"),key=lambda r:r["q"],reverse=True)
def xi_from(v,L):
    s1,s2=v[:2]
    x1=(2*math.sin(math.pi/L))**2;x2=(2*math.sin(2*math.pi/L))**2
    if s1<=s2:return None
    mass2=(s2*x2-s1*x1)/(s1-s2)
    if mass2<=0:return None
    return 1/math.sqrt(mass2)
def boot(path,func,nboot=2000,seed=7141):
    _,v=research.spectrum(research.read(ROOT/path))
    rng=np.random.default_rng(seed)
    out=[]
    for _ in range(nboot):
        mean=v[rng.integers(0,len(v),len(v))].mean(axis=0)
        y=func(mean)
        if y is not None and math.isfinite(y):out.append(float(y))
    out.sort()
    return {"valid_fraction":len(out)/nboot,
            "percentile_95_among_valid":[out[int(.025*len(out))],out[min(len(out)-1,int(.975*len(out)))]]}
def rgb(q):
    return {0.8:"#4978ba",0.5:"#27a38b",3/7:"#dc8c29",0.4:"#b95662"}.get(q,"#7554ad")
estimates=[]
for r in random_rows:
    L=r["L"]; s=r["S"]; q=r["q"];xi=xi_from(s,L)
    x=[(2*math.sin(math.pi*m/L))**2 for m in [1,2,3]]
    oz=None
    if xi is not None:
        m2=1/xi**2;A=s[0]*(x[0]+m2);pred=A/(x[2]+m2)
        flat=(s[0]+s[1])/2
        oz={"A":A,"xi":xi,"heldout_mode":3,"predicted_S3":pred,
            "observed_S3":s[2],"absolute_holdout_error":abs(pred-s[2]),
            "tested_modes":[1,2,3],"observed_sup_error_on_tested_modes":abs(pred-s[2]),
            "confidence_level_for_effective_law":None,
            "flat_holdout_error":abs(flat-s[2]),
            "diagnostic_pass":abs(pred-s[2])<abs(flat-s[2]) and
                 abs(pred-s[2])<=2*r["descriptive_se"][2]}
    ci=boot(r["path"],lambda v:xi_from(v,L)) if xi is not None else None
    estimates.append({"q":q,"L":L,"path":r["path"],"S":s,"S_se":r["descriptive_se"],
       "xi_fit":oz,"xi_bootstrap_descriptive":ci,
       "validity":"exploratory: unresolved initialization and mixing bias"})
base=next(r for r in random_rows if r["q"]==.8)
near=next(r for r in random_rows if abs(r["q"]-3/7)<1e-9)
high=next(r for r in random_rows if abs(r["q"]-.4)<1e-9)
rng=np.random.default_rng(784)
_,vbase=research.spectrum(research.read(ROOT/base["path"]))
_,vnear=research.spectrum(research.read(ROOT/near["path"]))
ratios=[]
for _ in range(2000):
    b=vbase[rng.integers(len(vbase),size=len(vbase)),0].mean()
    n=vnear[rng.integers(len(vnear),size=len(vnear)),0].mean()
    ratios.append(n/b)
ratios.sort()
scattering={"probe_q":[1,0,0],"L":12,"a_abs_squared":1,
 "geometry_coefficient":0.1,"intensity_far":base["S"][0],
 "intensity_near":near["S"][0],"intensity_below_candidate":high["S"][0],
 "near_far_ratio":near["S"][0]/base["S"][0],
 "ratio_bootstrap_descriptive_95":[ratios[50],ratios[1950]],
 "optical_depth_far":.1*base["S"][0],"optical_depth_near":.1*near["S"][0],
 "optical_depth_below_candidate":.1*high["S"][0],
 "exact_power_certificate":"results/exact_spectrum_intervals.json",
 "Lean_conditional_ratio_bound":[9,10],
 "classification":"synthetic accessible lattice wavevector; conditional weak-scattering probe"}
# An unconstrained fit on the five valid warm-side points.  It is diagnostic,
# not a confidence-certified critical exponent.
fitrows=[e for e in estimates if e["q"]<=.5 and e["q"]> .4 and e["xi_fit"]
         and e["xi_fit"]["diagnostic_pass"]]
q=np.array([r["q"] for r in fitrows]);y=np.log([r["xi_fit"]["xi"] for r in fitrows])
candidates=np.linspace(.39,min(q)-.0002,2000)
fits=[]
for qc in candidates:
    x=np.log(q-qc);slope,intercept=np.polyfit(x,y,1)
    rss=float(np.sum((y-(slope*x+intercept))**2))
    fits.append((rss,qc,-slope,math.exp(intercept)))
best=min(fits)
scaling={"model":"xi=C*(q-qc)^(-nu)","q_domain":[float(min(q)),float(max(q))],
 "q_c_grid_domain":[float(candidates[0]),float(candidates[-1])],
 "best":{"q_c":best[1],"nu":best[2],"C":best[3],"log_RSS":best[0]},
 "certified_parameter_intervals":{"q_c":None,"nu":None,"C":None},
 "status":"diagnostic fit only on holdout-passing points; initialization sensitivity and finite-size bias unbounded"}
derived={"analysis_source_sha256":research.sha(ROOT/"finalize.py"),
 "research_source_sha256":research.sha(ROOT/"research.py"),
 "simulator_source_sha256":research.sha(ROOT/"simulator.cpp"),
 "numerical_method":"numpy FFT for survey; exact Q(sqrt(3)) interval certificate for final L12 axis powers, with external bit-to-coefficient extraction",
 "bootstrap_note":"replica resampling quantifies sampling spread conditional on iid equilibrated replicas; it excludes mixing and model discrepancy",
 "estimates":estimates,"scaling":scaling,"scattering":scattering}
(OUT/"derived.json").write_text(json.dumps(derived,indent=2)+"\n")
manifest=[]
for path in sorted((ROOT/"data"/"raw").glob("*.jsonl")):
    rows=research.read(path)
    r=rows[0]
    manifest.append({"path":str(path.relative_to(ROOT)),"sha256":research.sha(path),
      "model_version":r["version"],"L":r["L"],"N":r["N"],
      "q":[r["q_num"],r["q_den"]],"replicas":len(rows),
      "burn_sweeps":r["burn_sweeps"],"aux_global_sweeps":r.get("aux_global_sweeps",0),
      "initial":r["initial"],"master_seed":r["master_seed"],
      "sampling":"one terminal state per independently seeded chain",
      "observables":"density Fourier mode powers, contacts, acceptance counters"})
(OUT/"manifest.json").write_text(json.dumps({"datasets":manifest,
 "simulator_source_sha256":research.sha(ROOT/"simulator.cpp"),
 "analysis_source_sha256":research.sha(ROOT/"research.py"),
 "exact_modes_source_sha256":research.sha(ROOT/"exact_modes.py"),
 "derived_source_sha256":research.sha(ROOT/"finalize.py")},indent=2)+"\n")
long_local=[research.summarize(p) for p in sorted((ROOT/"data"/"raw").glob("*B10000*.jsonl"))]
(OUT/"long_local.json").write_text(json.dumps(long_local,indent=2)+"\n")

def svg_plot(filename,title,xlab,ylab,series,logx=False,logy=False):
    W,H=760,480;ml,mr,mt,mb=78,25,55,70
    points=[(x,y) for _,xy,_ in series for x,y in xy if x>0 or not logx]
    def tx(x):return math.log10(x) if logx else x
    def ty(y):return math.log10(y) if logy else y
    xv=[tx(x) for x,y in points];yv=[ty(y) for x,y in points if y>0 or not logy]
    xmin,xmax=min(xv),max(xv);ymin,ymax=min(yv),max(yv)
    if xmin==xmax:xmax+=1
    if ymin==ymax:ymax+=1
    dx=xmax-xmin;dy=ymax-ymin;xmin-=.06*dx;xmax+=.06*dx;ymin-=.08*dy;ymax+=.08*dy
    def xy(x,y):
        return ml+(tx(x)-xmin)/(xmax-xmin)*(W-ml-mr),H-mb-(ty(y)-ymin)/(ymax-ymin)*(H-mt-mb)
    a=[f'<svg xmlns="http://www.w3.org/2000/svg" width="{W}" height="{H}" viewBox="0 0 {W} {H}">',
       '<rect width="100%" height="100%" fill="white"/>',
       f'<text x="{W/2}" y="29" text-anchor="middle" font-family="sans-serif" font-size="18">{title}</text>',
       f'<line x1="{ml}" y1="{H-mb}" x2="{W-mr}" y2="{H-mb}" stroke="#333"/>',
       f'<line x1="{ml}" y1="{mt}" x2="{ml}" y2="{H-mb}" stroke="#333"/>',
       f'<text x="{W/2}" y="{H-15}" text-anchor="middle" font-family="sans-serif">{xlab}</text>',
       f'<text transform="translate(18,{H/2}) rotate(-90)" text-anchor="middle" font-family="sans-serif">{ylab}</text>']
    for i in range(5):
        u=xmin+(xmax-xmin)*i/4;v=ymin+(ymax-ymin)*i/4
        X=ml+(W-ml-mr)*i/4;Y=H-mb-(H-mt-mb)*i/4
        xvlabel=10**u if logx else u;yvlabel=10**v if logy else v
        a+=[f'<text x="{X}" y="{H-mb+18}" text-anchor="middle" font-size="11" font-family="sans-serif">{xvlabel:.2g}</text>',
            f'<text x="{ml-9}" y="{Y+4}" text-anchor="end" font-size="11" font-family="sans-serif">{yvlabel:.2g}</text>']
    for si,(label,values,color) in enumerate(series):
        coords=[xy(x,y) for x,y in values if (x>0 or not logx) and (y>0 or not logy)]
        if len(coords)>1:a.append('<polyline fill="none" stroke="%s" stroke-width="2" points="%s"/>'%(color," ".join(f"{x:.2f},{y:.2f}" for x,y in coords)))
        for X,Y in coords:a.append(f'<circle cx="{X:.2f}" cy="{Y:.2f}" r="4" fill="{color}"/>')
        a.append(f'<text x="{W-175}" y="{mt+18*si}" font-size="12" fill="{color}" font-family="sans-serif">{label}</text>')
    a.append('</svg>')
    (PLOTS/filename).write_text("\n".join(a)+"\n")
chosen=[r for r in random_rows if r["q"] in [.8,.5,3/7,.4]]
svg_plot("structure_factor.svg","Measured structure factor, L=12","lattice wave number |k|","S(k)",
 [(f"q={r['q']:.3f}",[(2*math.pi*m/12,v) for m,v in zip(r["modes"],r["S"])],rgb(r["q"])) for r in chosen],logy=True)
valid=[e for e in estimates if e["xi_fit"] and e["q"]<=.5 and e["q"]>.4]
svg_plot("correlation_length.svg","Two-mode emergent length (exploratory)","q","xi / lattice spacing",
 [("random starts",[(e["q"],e["xi_fit"]["xi"]) for e in valid],"#276eaa")])
ref=load("refinement.json")
svg_plot("finite_size.svg","Lowest-mode growth across box sizes","L","S(k_min)",
 [(f"q={qq:.3f}",[(r["L"],r["S"][0]) for r in ref if abs(r["q"]-qq)<1e-9],rgb(qq))
  for qq in [.4,.375,1/3]],logx=True,logy=True)
qc=best[1];nu=best[2];C=best[3]
grid=np.linspace(min(q),max(q),60)
svg_plot("scaling_fit.svg","Unvalidated three-parameter scaling fit","q - fitted q_c","xi",
 [("measured",[(e["q"]-qc,e["xi_fit"]["xi"]) for e in valid],"#276eaa"),
  ("fit",[(float(v-qc),float(C*(v-qc)**(-nu))) for v in grid],"#c36c2e")],logx=True,logy=True)
svg_plot("scattering.svg","Synthetic probe: I = |a|² S(k_min)","q","relative scattered intensity",
 [("L=12, |a|²=1",[(r["q"],r["S"][0]) for r in reversed(random_rows)],"#ab4f83")],logy=True)

log=[
 {"id":"Q1","question":"When does a weak high-q low-k fluctuation hypothesis fail?",
  "experiment":"Five-point rational-q scan, L=6, independent seeded chains, 500 local sweeps.",
  "observation":"Event S_snapshot(k_min)>3 rose from 0/64 at q=4/5 to 53/64 at q=1/3.",
  "decision":"Refine the largest adjacent rise in measured S1, q=2/5 to 1/3.",
  "status":"Observed; conditional Hoeffding intervals require iid equilibrium replicas."},
 {"id":"Q2","question":"Is the rise confined by the box?",
  "experiment":"Controller-selected q=3/8 and adjacent controls, L=6,8,10,12.",
  "observation":"At q=2/5, S1 rose from 2.87 (L6) to 11.82 (L12).",
  "decision":"Probe warm side and test initialization sensitivity.",
  "status":"Observed finite-size dependence."},
 {"id":"Q3","question":"Can a single Ornstein-Zernike length explain the low modes?",
  "experiment":"Fit modes 1,2 and predeclare mode 3 as holdout.",
  "observation":"Positive length on warm side; at q=2/5 the random-start two-mode mass squared is negative.",
  "decision":"Restrict exploratory effective law to warm-side q and mark ordered-side failure.",
  "status":"Empirical model, not a theorem."},
 {"id":"Q4","question":"Do local Kawasaki chains forget their initial condition?",
  "experiment":"Random and slab starts, L=8,12, 2000 local sweeps, then L12 10000 sweeps.",
  "observation":"Material differences persisted, including q=3/7 and q=1/2.",
  "decision":"Introduce separately labeled global-swap burn and repeat start-state check.",
  "status":"Equilibrium claim rejected for these local runs."},
 {"id":"Q5","question":"Does auxiliary reversible equilibration erase the bias?",
  "experiment":"Global-swap burns of 1000 and 5000 sweeps followed by local Kawasaki 1000 sweeps, random/slab starts.",
  "observation":"At q=5/11 longer preparation narrowed the start gap, but at q=3/7 S1 remained 7.51 versus 4.93.",
  "decision":"Keep critical scaling and scattering estimates exploratory, with mixing bias unresolved.",
  "status":"Unresolved."},
 {"id":"Q6","question":"What would a weak linear density probe scatter?",
  "experiment":"Apply formally checked linear Fourier-amplitude identity to measured S(k_min).",
  "observation":f"Random-start auxiliary data give {scattering['near_far_ratio']:.2f}x near/far intensity ratio.",
  "decision":"Report synthetic accessible-k prediction conditional on probe and equilibration.",
  "status":"Conditional prediction."}
]
(OUT/"experiment_log.json").write_text(json.dumps(log,indent=2)+"\n")
nodes=[
 {"id":"model","kind":"assumed","claim":"3D periodic half-filled lattice gas, H=-contacts, q rational"},
 {"id":"lean_kernel","kind":"formally proved","claim":"finite state space, conservation, nonnegativity, normalized rows, detailed balance, stationarity","file":"LatticeGas.lean","depends_on":["model"]},
 {"id":"cpp","kind":"numerically checked","claim":"local-energy and count assertions on sampled moves; external implementation equivalence not proved","depends_on":["lean_kernel"]},
 {"id":"raw","kind":"recorded experiment","claim":"seeded JSONL snapshots and metadata","depends_on":["cpp"]},
 {"id":"estimator","kind":"numerically checked","claim":"FFT-based S(k) survey; direct DFT cross-check","depends_on":["raw"]},
 {"id":"exact_fourier","kind":"formally proved conditional","claim":"exact Q(sqrt(3)) L12 power interval and Lean 9-to-10 ratio bound given extracted integer coefficients","file":"LatticeGasNumerics.lean","depends_on":["raw"]},
 {"id":"stat","kind":"formally proved conditional","claim":"one-sided subGaussian confidence theorem under independence","file":"LatticeGasStats.lean","depends_on":["estimator"]},
 {"id":"xi","kind":"empirically inferred","claim":"warm-side two-mode OZ length, bootstrap sampling spread; mixing bias open","depends_on":["estimator","stat"]},
 {"id":"scattering_algebra","kind":"formally proved conditional","claim":"linear dielectric Fourier amplitude gives normSq(a) times density power","file":"LatticeGasScattering.lean","depends_on":["model"]},
 {"id":"probe","kind":"heuristic prediction","claim":"synthetic scattering enhancement at measured wavevector","depends_on":["estimator","exact_fourier","xi","scattering_algebra"]}
]
(OUT/"provenance.json").write_text(json.dumps({"nodes":nodes,
 "unclosed_edges":["C++ implementation ↔ Lean kernel","finite-burn equilibrium","raw-bit to exact-Fourier coefficient extraction",
                   "bootstrap coverage for nonlinear fit","finite-size extrapolation"]},indent=2)+"\n")
print(json.dumps({"scattering_ratio":scattering["near_far_ratio"],"scaling_fit":scaling["best"],
                  "xi":[[e["q"],e["xi_fit"]["xi"] if e["xi_fit"] else None] for e in estimates]},indent=2))
