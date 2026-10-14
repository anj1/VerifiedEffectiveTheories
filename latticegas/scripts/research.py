#!/usr/bin/env python3
"""Reproducible staged lattice-gas experiment. Raw JSONL files are immutable inputs."""
import argparse, hashlib, json, math, pathlib, subprocess
import numpy as np

ROOT = pathlib.Path(__file__).resolve().parent
RAW = ROOT / "data" / "raw"
OUT = ROOT / "results"
SIM = ROOT / "build" / "simulator"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def build():
    SIM.parent.mkdir(exist_ok=True)
    subprocess.run(["g++","-O3","-std=c++17",str(ROOT/"simulator.cpp"),"-o",str(SIM)],check=True)

def run(L,a,d,reps,burn,seed,initial="random"):
    RAW.mkdir(parents=True,exist_ok=True)
    path=RAW/f"L{L}_q{a}of{d}_{initial}_R{reps}_B{burn}_S{seed}.jsonl"
    if not path.exists():
        subprocess.run([str(SIM),str(L),str(a),str(d),str(reps),str(burn),
                        str(seed),initial,str(path),"100003"],check=True)
    return path

def run_aux(L,a,d,reps,global_burn,local_burn,seed,initial="random"):
    RAW.mkdir(parents=True,exist_ok=True)
    path=RAW/f"L{L}_q{a}of{d}_{initial}_R{reps}_G{global_burn}_B{local_burn}_S{seed}.jsonl"
    if not path.exists():
        subprocess.run([str(SIM),str(L),str(a),str(d),str(reps),str(local_burn),
                        str(seed),initial,str(path),"100003",str(global_burn)],check=True)
    return path

def read(path):
    rows=[json.loads(line) for line in path.read_text().splitlines()]
    assert rows and all(len(r["bits"])==r["L"]**3 for r in rows)
    assert all(r["bits"].count("1")==r["N"] for r in rows)
    return rows

def spectrum(rows):
    L=rows[0]["L"]; N=rows[0]["N"]
    modes=list(range(1,L//2+1))
    values=np.zeros((len(rows),len(modes)))
    for ri,r in enumerate(rows):
        s=np.fromiter((int(c) for c in r["bits"]),dtype=np.float64).reshape((L,L,L))
        ft=np.fft.fftn(s)
        for mi,m in enumerate(modes):
            vals=[]
            for axis in range(3):
                k=[0,0,0];k[axis]=m
                vals.append(abs(ft[tuple(k)])**2/N)
            values[ri,mi]=np.mean(vals)
    return modes,values

def summarize(path,alpha=.05,threshold=3.0):
    rows=read(path); modes,v=spectrum(rows)
    R=len(rows);N=rows[0]["N"]
    means=v.mean(axis=0); ses=v.std(axis=0,ddof=1)/math.sqrt(R)
    event=(v[:,0]>threshold).astype(float)
    # Hoeffding plus union bound across all predeclared scan points is applied
    # later; this per-point radius is marginal.
    rad=math.sqrt(math.log(2/alpha)/(2*R))
    return {"path":str(path.relative_to(ROOT)),"sha256":sha(path),
      "L":rows[0]["L"],"N":N,"q":rows[0]["q_num"]/rows[0]["q_den"],
      "q_num":rows[0]["q_num"],"q_den":rows[0]["q_den"],"R":R,
      "burn_sweeps":rows[0]["burn_sweeps"],"seed":rows[0]["master_seed"],
      "model_version":rows[0]["version"],
      "aux_global_sweeps":rows[0].get("aux_global_sweeps",0),
      "initial":rows[0]["initial"],"modes":modes,"S":means.tolist(),
      "descriptive_se":ses.tolist(),"event_threshold":threshold,
      "event_rate":float(event.mean()),
      "hoeffding_marginal_95":[max(0.,float(event.mean()-rad)),
                                min(1.,float(event.mean()+rad))],
      "acceptance_rate":float(np.mean([r["accepted"]/(r["burn_sweeps"]*r["L"]**3) for r in rows]))}

def stage1():
    build()
    # Coarse scan is intentionally broad, with no encoded transition location.
    qvals=[(4,5),(2,3),(1,2),(2,5),(1,3)]
    paths=[run(6,a,d,64,500,17911) for a,d in qvals]
    summaries=[summarize(p,alpha=.05/len(paths)) for p in paths]
    OUT.mkdir(exist_ok=True)
    (OUT/"scan.json").write_text(json.dumps(summaries,indent=2)+"\n")
    print(json.dumps([{"q":s["q"],"S1":s["S"][0],"event":s["event_rate"],
        "ci":s["hoeffding_marginal_95"]} for s in summaries],indent=2))

def stage2():
    scan=json.loads((OUT/"scan.json").read_text())
    # Ask where the rise is largest; automatically refine the adjacent q gap.
    ordered=sorted(scan,key=lambda x:x["q"],reverse=True)
    diffs=[ordered[i+1]["S"][0]-ordered[i]["S"][0] for i in range(len(ordered)-1)]
    i=int(np.argmax(diffs))
    hi,lo=ordered[i],ordered[i+1]
    # Rational mediant keeps acceptance arithmetic exact and avoids a
    # manually supplied critical q.
    a=hi["q_num"]+lo["q_num"];d=hi["q_den"]+lo["q_den"]
    from math import gcd
    g=gcd(a,d);a//=g;d//=g
    build()
    paths=[]
    for L in [6,8,10,12]:
        for qa,qd in [(hi["q_num"],hi["q_den"]),(a,d),(lo["q_num"],lo["q_den"])]:
            paths.append(run(L,qa,qd,64,1000,37291+L))
    summaries=[summarize(p,alpha=.05/len(paths)) for p in paths]
    (OUT/"refinement.json").write_text(json.dumps(
        {"selection":{"largest_adjacent_S1_increase":[hi["q"],lo["q"]],
                      "refinement_q":[a,d]},
         "data":summaries},indent=2)+"\n")
    print(json.dumps({"refinement_q":[a,d],
        "results":[{"L":s["L"],"q":s["q"],"S1":round(s["S"][0],3),
                    "event":s["event_rate"]} for s in summaries]},indent=2))

def stage3():
    scan=json.loads((OUT/"scan.json").read_text())
    refine=json.loads((OUT/"refinement.json").read_text())
    # Choose the warm-side neighbor of the largest-L refined point.  This is
    # prompted by continued growth with L, which may be phase separation.
    qedge=max(x["q"] for x in refine["data"])
    warm=min((x for x in scan if x["q"]>qedge),key=lambda x:x["q"])
    edge=next(x for x in scan if x["q"]==qedge)
    a=warm["q_num"]+edge["q_num"];d=warm["q_den"]+edge["q_den"]
    from math import gcd
    g=gcd(a,d);a//=g;d//=g
    build()
    paths=[]
    for L in [8,12]:
        for qa,qd in [(warm["q_num"],warm["q_den"]),(a,d),
                      (edge["q_num"],edge["q_den"])]:
            for initial in ["random","slab"]:
                paths.append(run(L,qa,qd,64,2000,50991+L,initial))
    summaries=[summarize(p,alpha=.05/len(paths)) for p in paths]
    (OUT/"warm_side.json").write_text(json.dumps(
        {"selection":{"question":"Is finite-size growth at the refined edge critical or ordered?",
                      "warm_side_mediant":[a,d]},"data":summaries},indent=2)+"\n")
    print(json.dumps([{"L":s["L"],"q":s["q"],"initial":s["initial"],
                       "S1":round(s["S"][0],3),"event":s["event_rate"]}
                      for s in summaries],indent=2))

def stage4():
    build()
    paths=[]
    for a,d in [(1,2),(3,7)]:
        for initial in ["random","slab"]:
            paths.append(run_aux(12,a,d,64,1000,1000,99217,initial))
    summaries=[summarize(p,alpha=.05/len(paths)) for p in paths]
    (OUT/"aux_equilibration.json").write_text(json.dumps(
        {"question":"Does an auxiliary reversible global-swap burn erase initial-state dependence?",
         "note":"The auxiliary kernel preserves the same canonical Gibbs distribution but is not the physical nearest-neighbor dynamics.",
         "data":summaries},indent=2)+"\n")
    print(json.dumps([{"q":s["q"],"initial":s["initial"],"S1":s["S"][0],
                       "S2":s["S"][1]} for s in summaries],indent=2))

def stage5():
    build()
    paths=[]
    for a,d in [(5,11),(3,7)]:
        for initial in ["random","slab"]:
            paths.append(run_aux(12,a,d,64,5000,1000,171029,initial))
    summaries=[summarize(p,alpha=.05/len(paths)) for p in paths]
    (OUT/"aux_longer.json").write_text(json.dumps(summaries,indent=2)+"\n")
    print(json.dumps([{"q":s["q"],"initial":s["initial"],"S1":s["S"][0],
                       "S2":s["S"][1]} for s in summaries],indent=2))

def main():
    ap=argparse.ArgumentParser();ap.add_argument("stage",choices=["stage1","stage2","stage3","stage4","stage5"])
    args=ap.parse_args()
    {"stage1":stage1,"stage2":stage2,"stage3":stage3,"stage4":stage4,
     "stage5":stage5}[args.stage]()
if __name__=="__main__":main()
