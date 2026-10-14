#!/usr/bin/env python3
"""Exhaustive exact-rational L=2 check of the mathematical bond kernel."""
import itertools, json, pathlib
from fractions import Fraction
L=2;V=L**3;N=V//2
def index(x,y,z):return (x*L+y)*L+z
def shift(i,c):
    x,y,z=i//(L*L),(i//L)%L,i%L
    if c==0:x=(x+1)%L
    if c==1:y=(y+1)%L
    if c==2:z=(z+1)%L
    return index(x,y,z)
bonds=[(i,shift(i,c)) for i in range(V) for c in range(3)]
def contacts(s):return sum(s[i]*s[j] for i,j in bonds)
def swap(s,i,j):
    t=list(s);t[i],t[j]=t[j],t[i]
    return tuple(t)
states=[]
for occupied in itertools.combinations(range(V),N):
    states.append(tuple(int(i in occupied) for i in range(V)))
where={s:i for i,s in enumerate(states)}
q=Fraction(1,2)
P=[]
for s in states:
    row={}
    for i,j in bonds:
        t=swap(s,i,j)
        de=contacts(s)-contacts(t)
        acc=q**max(0,de)
        row[t]=row.get(t,Fraction(0))+acc/len(bonds)
        row[s]=row.get(s,Fraction(0))+(1-acc)/len(bonds)
    assert sum(row.values())==1
    assert all(v>=0 for v in row.values())
    P.append(row)
for k,s in enumerate(states):
    ws=q**(-contacts(s))
    for t,p in P[k].items():
        wt=q**(-contacts(t))
        assert ws*p==wt*P[where[t]].get(s,Fraction(0))
out={"kind":"exhaustive_exact_rational_check","L":L,"N":N,
     "q":"1/2","states":len(states),"bonds":len(bonds),
     "rows_normalized":True,"nonnegative":True,"pairwise_detailed_balance":True,
     "scope":"Mathematical Python reference only; no proof of C++/Lean equivalence."}
path=pathlib.Path(__file__).resolve().parent/"results"/"small_kernel_check.json"
path.parent.mkdir(exist_ok=True)
path.write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out))
