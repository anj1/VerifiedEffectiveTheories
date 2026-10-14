"""Independent replay and tiny-volume exact-enumeration checks (not a proof of PRNG randomness)."""
import glob
import json
import math
import struct
from fractions import Fraction


def neighbours(L,x):
    a=x%L;b=x//L%L;c=x//(L*L)
    idx=lambda i,j,k:i+L*(j+L*k)
    return (idx((a+1)%L,b,c),idx((a-1)%L,b,c),
            idx(a,(b+1)%L,c),idx(a,(b-1)%L,c),
            idx(a,b,(c+1)%L),idx(a,b,(c-1)%L))


def replay(row):
    L=row['L'];V=L**3;a=row['r_num'];b=row['r_den'];M=row['rational_uniform_denominator']
    ns=[neighbours(L,x) for x in range(V)]
    lo=[0]*V;hi=[1]*V
    data=open(row['stream_path'],'rb').read()
    assert len(data)==12*row['horizon_updates']
    for site,u in struct.iter_unpack('<IQ',data):
        assert site<V and u<M
        for s in (lo,hi):
            count=sum(s[y] for y in ns[site])
            numerator=a**(6-count)*b**count
            denominator=numerator+a**count*b**(6-count)
            s[site]=int(u*denominator<M*numerator)
    assert lo==hi and row['success']
    h=14695981039346656037
    for bit in lo:h=((h^bit)*1099511628211)&((1<<64)-1)
    m=sum(2*x-1 for x in lo)
    assert h==row['state_fnv64']
    assert m==row['magnetization_sum']
    assert m*m==row['magnetization_sum_2']
    assert m**4==row['magnetization_sum_4']
    if 'disagreement_count' in row:
        D=sum(lo[x]!=lo[ns[x][j]] for x in range(V) for j in (0,2,4))
        assert D==row['disagreement_count']
    return {'path':row['stream_path'],'updates':row['horizon_updates'],'state_fnv64':h}


def exact_L2(a,b):
    L=2;V=8;r=Fraction(a,b)
    weights=[];m2=[];m4=[]
    for mask in range(1<<V):
        s=[(mask>>i)&1 for i in range(V)]
        D=sum(s[x]!=s[neighbours(L,x)[j]] for x in range(V) for j in (0,2,4))
        m=sum(2*x-1 for x in s)
        w=r**D
        weights.append(w);m2.append(w*Fraction(m*m,V*V));m4.append(w*Fraction(m**4,V**4))
    Z=sum(weights)
    return {'Z_num':Z.numerator,'Z_den':Z.denominator,
            'm2':str(sum(m2)/Z),'m4':str(sum(m4)/Z)}


def conditional_check_L2(a,b):
    L=2;V=8;r=Fraction(a,b);checked=0
    def D(s):return sum(s[x]!=s[neighbours(L,x)[j]] for x in range(V) for j in (0,2,4))
    for mask in range(1<<V):
        s=[(mask>>i)&1 for i in range(V)]
        for x in range(V):
            plus=s.copy();minus=s.copy();plus[x]=1;minus[x]=0
            lhs=r**D(plus)/(r**D(plus)+r**D(minus))
            count=sum(s[y] for y in neighbours(L,x))
            rhs=r**(6-count)/(r**(6-count)+r**count)
            assert lhs==rhs,(mask,x,lhs,rhs)
            checked+=1
    return {'r':f'{a}/{b}','configurations':256,'site_conditionals_checked':checked}


def main():
    rows=[]
    for path in glob.glob('grandcanonical_data/raw/*cftp*jsonl'):
        for line in open(path):
            row=json.loads(line)
            if row['stream_path'] and row['success']:rows.append(row)
    checked=[replay(row) for row in rows]
    result={'replayed_cftp_streams':checked,'exact_L2_r5_8':exact_L2(5,8),
            'heatbath_conditionals_L2':[conditional_check_L2(5,8),conditional_check_L2(2,3)]}
    with open('grandcanonical_results/validation.json','w') as f:json.dump(result,f,indent=2)
    print(json.dumps(result,indent=2))


if __name__=='__main__':main()
