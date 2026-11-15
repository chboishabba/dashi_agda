#!/usr/bin/env python3
"""16-window source-owned acoustic-envelope inverse fit with multiplicity control.
Source: user's original Filsinger reel, preprocessed and verified at 36-75s.
These arrays are acoustic PSD-window features, NOT electrical power/phase.
"""
import numpy as np
PEAKS=np.array([3.125,3.375,3.5,3.5,3.625,3.375,3.0,4.25,
                4.75,4.75,3.625,3.75,5.,5.,3.5,4.],float)
FRACTIONS=np.array([.273930941,.154757293,.255920876,.240467894,
 .143734023,.080528884,.168619287,.093150016,.099814722,
 .143329862,.110907058,.201329529,.281372843,.296285156,
 .294574559,.259756885],float)
def positive_fit(nperm=2000,seed=42):
    freq=2*PEAKS
    centers=np.linspace(6,10,81)
    grid=[(q,c) for q in (3,5,10,20) for c in centers]
    curves=np.array([1/(1+(2*q*(freq/c-1))**2) for q,c in grid])
    curves-=curves.mean(axis=1)[:,None]
    curves/=np.linalg.norm(curves,axis=1)[:,None]
    y=FRACTIONS-FRACTIONS.mean();y/=np.linalg.norm(y)
    corr=curves@y;gain=np.maximum(corr,0)**2
    best=np.argmax(gain);obs=float(gain[best])
    rng=np.random.default_rng(seed)
    null=np.array([np.max(np.maximum(curves@rng.permutation(y),0)**2)
                  for _ in range(nperm)])
    def qfixed(q):
        h=1/(1+(2*q*(freq/7.83-1))**2)
        h=(h-h.mean())/np.linalg.norm(h-h.mean())
        return float(max(h@y,0)**2)
    return dict(windows=len(freq),best_q=grid[best][0],
        best_center_hz=grid[best][1],best_r2=obs,
        fixed_q5_r2=qfixed(5),fixed_q20_r2=qfixed(20),
        permutation_adjusted_p=float((1+(null>=obs).sum())/(1+nperm)))
if __name__=="__main__":
    r=positive_fit()
    assert r["windows"]==16
    assert r["fixed_q5_r2"]==0
    assert r["permutation_adjusted_p"]>.05
    print("PASS source-selected inverse audio and positive-overlap negative control",r)
