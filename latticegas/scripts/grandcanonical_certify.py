"""High-precision certificate for the predeclared four-point Binder crossing.

The probabilistic ingredient is Maurer--Pontil (2009), Theorem 4, applied to
independent bounded m^2 and m^4 observations. Four points × two moments × two
tails = 16 events, each assigned alpha/16 with alpha=1/20. The mathematical
coverage is conditional on independent ideal random streams; the physical
artifacts use a deterministic PRNG and do not prove that assumption.
"""
import glob
import hashlib
import json
import math
from decimal import Decimal, getcontext, ROUND_FLOOR, ROUND_CEILING
from pathlib import Path

getcontext().prec=100
D=Decimal
ALPHA=D(1)/20
TAIL=ALPHA/16
LOG=(D(2)/TAIL).ln()
PAD=D('1e-9')
Q=D('1e-12')
ROOT=Path('grandcanonical_data/raw')


def down(x):return x.quantize(Q,rounding=ROUND_FLOOR)
def up(x):return x.quantize(Q,rounding=ROUND_CEILING)


def files_for(L,a,b):
    # Fixed-size fresh holdout, selected after the 20k exploratory pilot.
    # The pilot is never pooled into this confidence calculation.
    n=40000 if (a,b)==(5,8) else 80000
    paths=[ROOT/f'cftp_L{L}_r{a}_{b}_n{n}.jsonl']
    assert all(p.is_file() for p in paths),paths
    return paths


def read_point(L,a,b):
    rows=[];paths=files_for(L,a,b)
    for path in paths:
        expected=int(path.stem.rsplit('_n',1)[1])
        with path.open() as f:batch=[json.loads(line) for line in f]
        assert len(batch)==expected,(path,len(batch),expected)
        rows.extend(batch)
    assert len({r['seed'] for r in rows})==len(rows)
    assert all(r['model_version']=='grandcanonical-v2' and r['ensemble']=='zero_field_ising'
               and r['algorithm']=='cftp' and r['L']==L and r['r_num']==a and r['r_den']==b
               and r['success'] for r in rows)
    return rows,paths


def bound(values,scale):
    n=len(values)
    s1=sum(values);s2=sum(x*x for x in values)
    mean=D(s1)/(D(n)*D(scale))
    variance=D(n*s2-s1*s1)/(D(n*(n-1))*D(scale)**2)
    assert variance>=0
    rad=(D(2)*variance*LOG/D(n)).sqrt()+D(7)*LOG/(D(3)*D(n-1))
    lo=down(max(D(0),mean-rad-PAD))
    hi=up(min(D(1),mean+rad+PAD))
    # Independent binary64 evaluation is a diagnostic, never the trusted endpoint.
    mf=s1/(n*scale)
    vf=(n*s2-s1*s1)/(n*(n-1)*scale*scale)
    rf=math.sqrt(2*vf*math.log(640)/n)+7*math.log(640)/(3*(n-1))
    assert abs(float(mean)-mf)<1e-12 and abs(float(rad)-rf)<1e-12
    return {'mean':str(mean),'sample_variance':str(variance),
            'interval':[str(lo),str(hi)],'radius':str(rad)}


def binder_interval(x2,x4):
    l2,u2=map(D,x2['interval']);l4,u4=map(D,x4['interval'])
    assert l2>0
    return [str(down(D(1)-u4/(D(3)*l2*l2)-PAD)),
            str(up(D(1)-l4/(D(3)*u2*u2)+PAD))]


def main():
    points={}
    all_paths=[]
    for L in (4,6):
        for a,b in ((5,8),(2,3)):
            rows,paths=read_point(L,a,b);all_paths+=paths
            V=L**3
            x2=bound([r['magnetization_sum_2'] for r in rows],V**2)
            x4=bound([r['magnetization_sum_4'] for r in rows],V**4)
            horizon=[r['horizon_updates'] for r in rows]
            points[f'L{L}_r{a}_{b}']={'L':L,'r':[a,b],'n':len(rows),
                'm2':x2,'m4':x4,'binder_interval':binder_interval(x2,x4),
                'horizon_min':min(horizon),'horizon_max':max(horizon),
                'horizon_median':sorted(horizon)[len(horizon)//2],
                'raw_files':[str(p) for p in paths]}
    differences={}
    for a,b in ((5,8),(2,3)):
        p4=points[f'L4_r{a}_{b}'];p6=points[f'L6_r{a}_{b}']
        l4,u4=map(D,p4['binder_interval']);l6,u6=map(D,p6['binder_interval'])
        differences[f'{a}/{b}']=[str(down(l4-u6-PAD)),str(up(u4-l6+PAD))]
    low=map(D,differences['5/8']);high=map(D,differences['2/3'])
    low=list(low);high=list(high)
    crossing=low[1]<0 and high[0]>0
    artifacts={}
    for p in all_paths+[Path('grandcanonical.cpp'),Path('GrandCanonical.lean'),
                         Path('grandcanonical_certify.py'),Path('grandcanonical_analysis.py')]:
        artifacts[str(p)]=hashlib.sha256(p.read_bytes()).hexdigest()
    cert={'model':'grandcanonical-v2','ensemble':'zero_field_ising',
          'claim':'finite_volume_Binder_crossing_L4_L6','familywise_alpha':'0.05',
          'per_one_sided_event_alpha':str(TAIL),
          'design':'The 20k-per-point pilot selected fresh holdout sizes; only holdout seeds (master 31427182) enter this certificate. Conditional coverage is valid given the pilot under ideal stream independence.',
          'coverage_statement':'P(all four Binder interval bounds contain their exact finite-volume targets) >= 0.95, conditional on iid exact CFTP output and Maurer-Pontil Theorem 4',
          'external_statistical_theorem':'https://www.cs.mcgill.ca/~colt2009/papers/012.pdf',
          'numeric_method':'exact integer raw moments; Decimal precision 100 for ln/sqrt; outward 12-digit rounding plus 1e-9 guard; binary64 cross-check',
          'numeric_rigor_limit':'Decimal transcendental-rounding guarantee not formalized in Lean; crossing margins exceed 1e-2',
          'points':points,'difference_intervals':differences,'sign_change':crossing,
          'conclusion_if_assumptions_hold':
            'There exists an r in (5/8,2/3) where exact finite-volume Binder curves for L=4 and L=6 cross; no infinite-volume criticality or exponent follows.',
          'artifacts_sha256':artifacts}
    Path('grandcanonical_results').mkdir(exist_ok=True)
    Path('grandcanonical_results/binder_crossing_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
    print(json.dumps({'difference_intervals':differences,'sign_change':crossing,
                      'n':{k:v['n'] for k,v in points.items()}},indent=2))
    assert crossing


if __name__=='__main__':main()
