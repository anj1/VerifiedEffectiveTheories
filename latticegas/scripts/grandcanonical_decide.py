"""Data-driven scout decision; contains no textbook critical parameter."""
import json
from fractions import Fraction
from pathlib import Path

INITIAL={(3,5),(5,8),(2,3),(7,10)}


def main():
    analysis=json.loads(Path('grandcanonical_results/analysis.json').read_text())
    scout={(p['L'],p['r_num'],p['r_den']):p for p in analysis['scout']}
    candidates=[]
    grid=sorted(INITIAL,key=lambda x:Fraction(*x))
    for a,b in zip(grid,grid[1:]):
        p4a,p6a=scout[(4,*a)],scout[(6,*a)]
        p4b,p6b=scout[(4,*b)],scout[(6,*b)]
        da=p4a['U4']-p6a['U4'];db=p4b['U4']-p6b['U4']
        if da*db<0:candidates.append((a,b,da,db))
    if not candidates:raise RuntimeError('no Binder sign bracket; request wider scan')
    a,b,da,db=min(candidates,key=lambda item:float(Fraction(*item[1])-Fraction(*item[0])))
    mediant=Fraction(a[0]+b[0],a[1]+b[1])
    log={
      'protocol':'grandcanonical-v2; scout only; no known critical value supplied',
      'questions_and_decisions':[
        {'question':'Does a dimensionless Binder size difference change sign across the broad rational scan?',
         'hypothesis':'At high r, low-k fluctuations and finite-size ordering are weak.',
         'experiment':'SW 200 separately seeded chains per L and r, 160+20 sweeps; L=4,6,8,12,16; r=3/5,5/8,2/3,7/10.',
         'observation':{'L4_minus_L6_at_left':da,'L4_minus_L6_at_right':db,
                        'bracket':[f'{a[0]}/{a[1]}',f'{b[0]}/{b[1]}']},
         'decision':f'Ask for additional SW points at the mediant {mediant.numerator}/{mediant.denominator} and exact CFTP at the bracket endpoints.',
         'epistemic_status':'heuristic SW scout; equilibrium not certified'},
        {'question':'Was the independent-replica assumption valid in the first implementation?',
         'experiment':'Enumerate all 256 L=2 states exactly and compare moments with SW and CFTP.',
         'observation':'Version 1 arithmetic replica seeds produced shifted, overlapping SplitMix64 streams; both samplers disagreed with enumeration. Version 2 hashes replica identifiers and agrees in validation.',
         'decision':'Archive all version-1 output under grandcanonical_data/invalid_v1; restart the scout and keep only version-2 data for inference.',
         'epistemic_status':'diagnostic numerical validation, not a randomness proof'},
        {'question':'Can exact-sampling finite-volume Binder intervals certify a size crossing?',
         'experiment':'Exploratory CFTP 20,000 replicas per endpoint and L=4,6; then fresh holdout of 40,000 at r=5/8 and 80,000 at r=2/3 per size.',
         'observation':'All holdout replicas coalesced. Pilot and holdout are not pooled for the fixed-n confidence calculation.',
         'decision':'Compute familywise 95% moment intervals on the fresh holdout only, propagate through Binder, and test endpoint signs.',
         'epistemic_status':'probabilistic conditional on ideal independent streams; empirical-Bernstein theorem external to Lean'},
        {'question':'Where should the next exact experiment concentrate?',
         'experiment':f'CFTP at the scout-refined rational parameter {mediant.numerator}/{mediant.denominator} for L=6,8,12 if coalescence remains tractable.',
         'observation':'The current certified bracket is finite-volume only; scaling exponents are unmeasured.',
         'decision':'Do not fit nu or eta yet; first acquire a second crossing pair and check size drift.',
         'epistemic_status':'proposed experiment'}]}
    Path('grandcanonical_data/experiment_log.json').write_text(json.dumps(log,indent=2)+'\n')
    print(json.dumps(log['questions_and_decisions'][0],indent=2))


if __name__=='__main__':main()
