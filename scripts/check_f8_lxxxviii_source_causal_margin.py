"""LXXXVIII original-FV versus weak-source four-way physical-geometry preflight.

Run locally on literal clean original GitHub source. No propagation and no CI.
Records original cell-mass conservation, source support, photon guard margin,
and same-grid producer nonidentity. Not a production 96-output acceptance.
"""
import json,math
import numpy as np
from ksw668_f8_tt_multipole import F
from ksw668_f8_fv_source_flux import exact_cell_averages,total_scaled_moments
from ksw668_f8_weak_source import weak_source

def evaluate():
    eps=.04
    final_t=12.
    span=F(final_t)-F(1.)
    bulk=math.sqrt(span*span-(1-1/final_t)**2)
    near=bulk-.012
    far=bulk+.1
    target=total_scaled_moments()
    reports=[]
    arrays={}
    for label in ("A0","A1","C0","C1"):
        dr=.008 if label[0]=="A" else .006
        nr=int(math.ceil(3.01/dr))+1
        r=np.arange(nr)*dr
        src=weak_source(eps,r,dr) if label[-1]=="1" else exact_cell_averages(eps,r,dr)
        arrays[label]=src
        assert src.shape==(3,nr) and np.isfinite(src).all()
        moments=[]
        for q,ell in enumerate((0,2,4)):
            d=3+2*ell
            w=((r+dr/2)**d-np.maximum(0,r-dr/2)**d)/d
            moments.append(float(np.dot(w,src[q])/eps**d))
        assert abs(moments[0])<1e-7 and abs(moments[1])<1e-7
        assert abs(moments[2]-target["l4"])<1e-7
        support=np.flatnonzero(np.any(src!=0,axis=0))
        assert support.size>3
        endpoint=float(r[support[-1]])
        guard=near-eps-math.log(final_t)-dr/2
        assert guard>0
        hat=near-math.log(final_t)-(endpoint+dr)-dr/2
        if label[-1]=="1":assert hat>0
        reports.append(dict(label=label,dr=dr,normalized_moments=moments,
            support_first=int(support[0]),support_last=int(support[-1]),
            support_last_r=endpoint,max_abs_source=float(np.max(abs(src))),
            original_FV_photon_guard_margin=guard,
            weak_source_hat_guard_margin=hat if label[-1]=="1" else None))
    differences=[]
    for old,new in (("A0","A1"),("C0","C1")):
        a,b=arrays[old],arrays[new]
        differences.append(dict(labels=[old,new],max_abs_difference=float(np.max(abs(a-b))),
            l2_difference=float(np.linalg.norm(a-b))))
    return dict(status="PASS",scope="ORIGINAL source preflight only, NOT propagation, native 96 output or continuum convergence",near_r=near,far_r=far,cases=reports,producer_differences=differences)
if __name__=="__main__":
    print(json.dumps(evaluate(),indent=2))
