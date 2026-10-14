#!/usr/bin/env python3
"""Independent direct-DFT check of selected FFT observables (not a formal bound)."""
import json, math, pathlib
import numpy as np
import research
root=pathlib.Path(__file__).resolve().parent
files=[]
for name in ["aux_more.json","aux_equilibration.json","aux_scaling.json","aux_longer.json"]:
    obj=json.loads((root/"results"/name).read_text())
    files.extend(obj["data"] if isinstance(obj,dict) else obj)
maximum=0.0;checks=0
for item in files:
    rows=research.read(root/item["path"])
    L=item["L"];N=item["N"]
    phase=np.exp(-2j*math.pi*np.arange(L)/L)
    for r in rows:
        s=np.fromiter((int(c) for c in r["bits"]),float).reshape((L,L,L))
        fft=np.fft.fftn(s)
        for m in [1,2,3]:
            for axis in range(3):
                k=[0,0,0];k[axis]=m
                direct=np.dot(s.sum(axis=tuple(i for i in range(3) if i!=axis)),
                              phase**m)
                diff=abs(abs(direct)**2/N-abs(fft[tuple(k)])**2/N)
                maximum=max(maximum,float(diff));checks+=1
out={"method":"direct complex DFT versus numpy FFT","checks":checks,
     "maximum_absolute_S_difference":maximum,
     "status":"independent floating-point cross-check; no formal rounding bound"}
(root/"results"/"numerical_check.json").write_text(json.dumps(out,indent=2)+"\n")
print(json.dumps(out))
