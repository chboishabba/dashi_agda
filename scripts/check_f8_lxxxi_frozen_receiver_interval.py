"""LXXXI conditional exact-rational frozen-receiver interval.
Evidence NPZ: K (6,3,3,13), weak/native_fv (3,13), from native #1530.
Reuses certified weak source enclosure; does NOT certify original FV emitter,
binary64 adjoint construction, or physical PDE propagation.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse,json,numpy as np
from check_f8_lxxv_taylor import enclose

def check(evidence):
    d=np.load(evidence)
    K,weak,fv=d['K'],d['weak'],d['native_fv']
    assert K.shape==(6,3,3,13) and weak.shape==fv.shape==(3,13)
    h=Q(1,5); bounds=enclose(h)
    box=[]
    for q in range(3):
        power=3+4*q
        for j in range(13):
            if j<=5:
                lo,hi=bounds[q][j]
                W=((j*h+h/2)**power-max(Q(0),j*h-h/2)**power)/power
                assert lo<=Q(float(weak[q,j]))*W<=hi,(q,j)
                box.append((lo/W,hi/W))
            else:
                assert weak[q,j]==0
                box.append((Q(0),Q(0)))
    rows=[]
    for channel in range(6):
        for mode in range(3):
            low=high=nom=model=Q(0)
            for q in range(3):
                for j in range(13):
                    c=Q(float(K[channel,mode,q,j]))
                    l,u=box[q*13+j]
                    low+=min(c*l,c*u);high+=max(c*l,c*u)
                    nom+=c*Q(float(weak[q,j]))
                    model+=c*(Q(float(fv[q,j]))-Q(float(weak[q,j])))
            assert low<=nom<=high
            rows.append(dict(channel=channel,mode=mode,
                lower=float(low),upper=float(high),
                nominal=float(nom),fv_minus_weak=float(model)))
    width=max(x['upper']-x['lower'] for x in rows)
    mismatch=max(abs(x['fv_minus_weak']) for x in rows)
    return dict(max_interval_width=width,max_native_fv_weak_gap=mismatch,
       gap_over_width=mismatch/width,rows=rows,
       scope='Frozen binary64 sensitivity treated as exact rational; no floating PDE/error certification')
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('npz',type=Path)
    a=p.parse_args();print(json.dumps(check(a.npz),indent=2))
