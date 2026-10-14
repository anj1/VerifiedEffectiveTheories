"""Grand-canonical analysis; never reads the canonical data tree.

SW observations are scouting diagnostics, not certified equilibrium samples.
CFTP intervals use the i.i.d. ideal-stream assumption and Maurer--Pontil's
two-sided empirical Bernstein bound with a Bonferroni correction. The Lean
proof currently covers deterministic CFTP coupling and rational algebra, not
the empirical Bernstein inequality itself. Ordinary float evaluation here
is padded by 1e-10, not a formal interval-arithmetic certificate.
"""
import glob
import json
import math
import os
import re
from collections import defaultdict
from fractions import Fraction
from grandcanonical_validate import exact_L2

ROOT = "grandcanonical_data/raw"
OUT = "grandcanonical_results"
ALPHA = 0.05


def load(pattern):
    out = []
    for path in sorted(glob.glob(os.path.join(ROOT, pattern))):
        with open(path) as stream:
            rows = [json.loads(line) for line in stream]
        if not rows:
            continue
        for row in rows:
            assert row["ensemble"] == "zero_field_ising"
            assert row["model_version"] == "grandcanonical-v2"
            assert row["L"] == rows[0]["L"]
            assert (row["r_num"], row["r_den"]) == (rows[0]["r_num"], rows[0]["r_den"])
        out.append((path, rows))
    return out


def moments(rows):
    good = [x for x in rows if x["success"]]
    if not good:
        return None
    L = rows[0]["L"]
    V = L**3
    x2 = [x["magnetization_sum_2"] / V**2 for x in good]
    x4 = [x["magnetization_sum_4"] / V**4 for x in good]
    mean2, mean4 = sum(x2)/len(x2), sum(x4)/len(x4)
    s0 = V*mean2
    sk = sum(sum(x["sk_axis_numerators"])/3/V for x in good)/len(good)
    return {
        "n": len(good), "n_censored": len(rows)-len(good),
        "m2": mean2, "m4": mean4,
        "U4": 1-mean4/(3*mean2**2) if mean2 else None,
        "S0": s0, "Sk_min": sk,
        "xi2_over_L": math.sqrt(max(s0/sk-1,0))/(2*L*math.sin(math.pi/L)) if sk else None,
        "m2_samples": x2, "m4_samples": x4,
    }


def ebernstein(xs, delta):
    n = len(xs)
    mean = sum(xs)/n
    variance = sum((x-mean)**2 for x in xs)/(n-1)
    log = math.log(2/delta)
    radius = math.sqrt(2*variance*log/n) + 7*log/(3*(n-1)) + 1e-10
    return [max(0,mean-radius), min(1,mean+radius)], radius


def hoeffding(xs, delta):
    n = len(xs)
    mean = sum(xs)/n
    radius = math.sqrt(math.log(2/delta)/(2*n)) + 1e-10
    return [max(0,mean-radius),min(1,mean+radius)],radius


def binder_interval(m2, m4):
    if m2[0] <= 0:
        return None
    return [1-m4[1]/(3*m2[0]**2),1-m4[0]/(3*m2[1]**2)]


def svg_lines(path, title, ylabel, series, xlabel="r = exp(-2K)"):
    width,height=780,470
    margin=(70,30,50,60)
    values=[(x,y) for pts in series.values() for x,y in pts if y is not None and math.isfinite(y)]
    if not values:return
    xmin,xmax=min(x for x,_ in values),max(x for x,_ in values)
    ymin,ymax=min(y for _,y in values),max(y for _,y in values)
    dy=(ymax-ymin) or 1
    ymin-=.08*dy;ymax+=.08*dy
    def X(v):return margin[0]+(v-xmin)/(xmax-xmin or 1)*(width-margin[0]-margin[1])
    def Y(v):return height-margin[3]-(v-ymin)/(ymax-ymin)*(height-margin[2]-margin[3])
    colors=["#1261a0","#e67e22","#249044","#9b59b6","#bb3344","#555555"]
    parts=[f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
           '<rect width="100%" height="100%" fill="white"/>',
           f'<text x="{width/2}" y="24" text-anchor="middle" font-size="19">{title}</text>',
           f'<line x1="{margin[0]}" y1="{height-margin[3]}" x2="{width-margin[1]}" y2="{height-margin[3]}" stroke="black"/>',
           f'<line x1="{margin[0]}" y1="{margin[2]}" x2="{margin[0]}" y2="{height-margin[3]}" stroke="black"/>',
           f'<text x="{width/2}" y="{height-12}" text-anchor="middle">{xlabel}</text>',
           f'<text x="18" y="{height/2}" transform="rotate(-90 18 {height/2})" text-anchor="middle">{ylabel}</text>']
    for i in range(6):
        y=ymin+(ymax-ymin)*i/5
        parts.append(f'<text x="{margin[0]-8}" y="{Y(y)+4:.2f}" text-anchor="end" font-size="11">{y:.2f}</text>')
    for i in range(6):
        x=xmin+(xmax-xmin)*i/5
        parts.append(f'<text x="{X(x):.2f}" y="{height-margin[3]+17}" text-anchor="middle" font-size="11">{x:.3f}</text>')
    for j,(name,pts) in enumerate(sorted(series.items())):
        pts=sorted((x,y) for x,y in pts if y is not None and math.isfinite(y))
        color=colors[j%len(colors)]
        if len(pts)>1:
            path_data=" ".join(f'{X(x):.1f},{Y(y):.1f}' for x,y in pts)
            parts.append(f'<polyline points="{path_data}" fill="none" stroke="{color}" stroke-width="2"/>')
        for x,y in pts:parts.append(f'<circle cx="{X(x):.1f}" cy="{Y(y):.1f}" r="4" fill="{color}"/>')
        parts.append(f'<text x="{width-120}" y="{48+18*j}" fill="{color}" font-size="13">{name}</text>')
    parts.append('</svg>')
    with open(path,"w") as f:f.write("\n".join(parts))


def main():
    os.makedirs(OUT,exist_ok=True)
    scout=[]
    for path,rows in load("sw_L*_r*.jsonl"):
        if "test_" in path:continue
        m=moments(rows)
        scout.append({"path":path,"L":rows[0]["L"],"r_num":rows[0]["r_num"],"r_den":rows[0]["r_den"],
                      "r":rows[0]["r_num"]/rows[0]["r_den"],"n":m["n"],
                      "U4":m["U4"],"xi2_over_L":m["xi2_over_L"],"S0":m["S0"],"Sk_min":m["Sk_min"],
                      "status":"scouting_only_burn_unverified"})
    points=[]
    jobs=load("cftp_L*_r*_n*.jsonl")
    jobs=[(path,rows) for path,rows in jobs if len(rows)==int(re.search(r'_n(\d+)\.jsonl$',path).group(1))]
    jobs=[(path,rows) for path,rows in jobs if len(rows)==
          (40000 if (rows[0]['r_num'],rows[0]['r_den'])==(5,8) else 80000)]
    grouped=defaultdict(lambda:{'paths':[],'rows':[]})
    for path,rows in jobs:
        key=(rows[0]['L'],rows[0]['r_num'],rows[0]['r_den'])
        grouped[key]['paths'].append(path)
        grouped[key]['rows'].extend(rows)
    delta=ALPHA/(max(1,len(grouped))*4) # two moments, two tails, all points
    for job in grouped.values():
        path=job['paths'];rows=job['rows']
        m=moments(rows)
        if not m:continue
        complete=m["n_censored"]==0
        e2,_=ebernstein(m["m2_samples"],delta) if m["n"]>=2 else ([0,1],0)
        e4,_=ebernstein(m["m4_samples"],delta) if m["n"]>=2 else ([0,1],0)
        h2,_=hoeffding(m["m2_samples"],delta)
        h4,_=hoeffding(m["m4_samples"],delta)
        points.append({"path":path,"L":rows[0]["L"],"r_num":rows[0]["r_num"],"r_den":rows[0]["r_den"],
                       "r":rows[0]["r_num"]/rows[0]["r_den"],"n":m["n"],"n_censored":m["n_censored"],
                       "U4":m["U4"],"xi2_over_L":m["xi2_over_L"],"S0":m["S0"],"Sk_min":m["Sk_min"],
                       "m2_mean":m["m2"],"m4_mean":m["m4"],
                       "m2_ebernstein":e2,"m4_ebernstein":e4,"U4_ebernstein":binder_interval(e2,e4),
                       "U4_hoeffding":binder_interval(h2,h4),
                       "status":"conditional_iid_exact_CFTP" if complete else "censored_no_unbiased_estimate"})
    crossings=[]
    by={(p["L"],p["r_num"],p["r_den"]):p for p in points}
    for L1,L2 in [(4,6),(6,8),(6,12)]:
        shared=sorted({(p["r_num"],p["r_den"]) for p in points if p["L"]==L1} &
                      {(p["r_num"],p["r_den"]) for p in points if p["L"]==L2},key=lambda t:t[0]/t[1])
        for a,b in zip(shared,shared[1:]):
            pa1,pa2=by[(L1,*a)],by[(L2,*a)]
            pb1,pb2=by[(L1,*b)],by[(L2,*b)]
            Ia=[pa1["U4_ebernstein"][0]-pa2["U4_ebernstein"][1],pa1["U4_ebernstein"][1]-pa2["U4_ebernstein"][0]]
            Ib=[pb1["U4_ebernstein"][0]-pb2["U4_ebernstein"][1],pb1["U4_ebernstein"][1]-pb2["U4_ebernstein"][0]]
            crossings.append({"sizes":[L1,L2],"r_interval":[f"{a[0]}/{a[1]}",f"{b[0]}/{b[1]}"],
                              "difference_intervals":[Ia,Ib],
                              "certified_sign_change":(Ia[1]<0 and Ib[0]>0) or (Ia[0]>0 and Ib[1]<0)})
    exact_l2=[]
    for p in points:
        if p['L']!=6 or p['status']!='conditional_iid_exact_CFTP':continue
        exact=exact_L2(p['r_num'],p['r_den'])
        m2=Fraction(exact['m2']);m4=Fraction(exact['m4'])
        binder=1-m4/(3*m2*m2)
        difference=[float(binder)-p['U4_ebernstein'][1],float(binder)-p['U4_ebernstein'][0]]
        exact_l2.append({'r':f"{p['r_num']}/{p['r_den']}",'U4_exact_fraction':str(binder),
                         'U4_exact_minus_L6_interval':difference,
                         'exact_method':'exhaustive_256_spin_enumeration_with_Fraction'})
    exact_l2.sort(key=lambda x:Fraction(x['r']))
    if len(exact_l2)>=2:
        a,b=exact_l2[0],exact_l2[-1]
        crossings.append({'sizes':[2,6],'r_interval':[a['r'],b['r']],
                          'difference_intervals':[a['U4_exact_minus_L6_interval'],b['U4_exact_minus_L6_interval']],
                          'certified_sign_change':a['U4_exact_minus_L6_interval'][1]<0 and b['U4_exact_minus_L6_interval'][0]>0,
                          'scope_note':'L=2 has parallel periodic edges; this is a finite-volume crossing, not an asymptotic critical-point estimate'})
    result={"model":"zero_field_ising_grand_canonical","alpha_family":ALPHA,
            "design":"fresh fixed-size holdout only; 20k pilot excluded",
            "interval_method":"Maurer-Pontil_2009_Theorem_4_two_sided_Bonferroni",
            "conditional_assumptions":["independent ideal unbiased random streams across CFTP replicas",
                                      "every CFTP replica coalesces; no success-only selection",
                                      "published empirical Bernstein theorem, not yet formalized in Lean",
                                      "float interval endpoints padded by 1e-10, not formally rounded"],
            "scout":scout,"cftp":points,"exact_L2":exact_l2,"crossings":crossings}
    with open(os.path.join(OUT,"analysis.json"),"w") as f:json.dump(result,f,indent=2)
    for name,label,key in [("binder.svg","Binder U4","U4"),("xi2_over_L.svg","xi2/L","xi2_over_L"),
                           ("scattering_skmin.svg","S(kmin) / spin","Sk_min")]:
        series=defaultdict(list)
        for p in scout:series[f"SW L={p['L']}"].append((p["r"],p[key]))
        svg_lines(os.path.join(OUT,name),label+" (SW scouting; not certified equilibrium)",label,series)
    if points:
        series=defaultdict(list)
        for p in points:series[f"CFTP L={p['L']}"].append((p['r'],p['U4']))
        svg_lines(os.path.join(OUT,'binder_cftp.svg'),
                  'Binder U4 (CFTP point estimates; intervals in JSON)','U4',series)
        series=defaultdict(list)
        for p in points:series[f"L={p['L']}, r={p['r_num']}/{p['r_den']}"]=[
            (0,p['S0']),(2*math.pi/p['L'],p['Sk_min'])]
        svg_lines(os.path.join(OUT,'two_mode_structure_factor.svg'),
                  'Spin structure factor: only k=0 and kmin','S_spin(k)',series,
                  xlabel='|k| in lattice units')
        series=defaultdict(list)
        for p in points:series[f"CFTP L={p['L']}"].append((p['r'],p['Sk_min']/4))
        svg_lines(os.path.join(OUT,'synthetic_probe.svg'),
                  'Synthetic density probe, |a|=1 (normalised intensity)',
                  'I/(|a|^2 V) = S_spin(kmin)/4',series)
    return result


if __name__=="__main__":
    result=main()
    print(json.dumps({"scout_points":len(result["scout"]),"cftp_points":len(result["cftp"]),
                      "crossings":result["crossings"]},indent=2))
