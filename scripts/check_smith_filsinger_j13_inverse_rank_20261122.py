#!/usr/bin/env python3
"""J13 conditional S3/S5 restored-cycle inverse-rank (dimensionless synthetic).
Uses the repository's J12 local solver; no Filsinger measurement claims.
"""
import json, math, numpy as np
from check_smith_filsinger_j12_restored_cycles_20261122 import BASE, periodic

OBS=['driver','incident','outgoing','spark','diode']
NAMES=['source_amp','phase','k','Von','Vd']
P=BASE|dict(Von=.003,Voff=.0009,source_amp=.1)
PHASE=.3
def sample(name,p,phase=PHASE,source=True):
    x=periodic(p,source,phase,max_iter=28,tol=2e-6)
    assert x['closure']<2e-6 and abs(x['storage_delta'])<1e-5 and abs(x['residual'])<1e-6
    return dict(case=name,phase=phase,source=source,**{key:x[key] for key in OBS+['net_wave','closure','residual','storage_delta','switches']})

def main():
    rows=[sample('baseline',P),sample('driver_only',P,source=False)]
    for a in (0.,.1,.4): rows.append(sample(f'amplitude_{a}',P|dict(source_amp=a)))
    for von,voff in ((.003,.0009),(.006,.0018),(.012,.0036),(.22,.075)):
        rows.append(sample(f'threshold_{von}',P|dict(Von=von,Voff=voff)))
    for k in (.1,.2): rows.append(sample(f'coupling_{k}',P|dict(k=k)))
    for ph in (0.,math.pi): rows.append(sample(f'phase_{ph}',P,ph))
    steps=dict(source_amp=.005,phase=.08,k=.005,Von=.00015,Vd=.005)
    columns=[];stencils=[]
    for param in NAMES:
        h=steps[param]
        if param=='phase':
            plus=sample('plus',P,PHASE+h);minus=sample('minus',P,PHASE-h)
        else:
            plus=sample('plus',P|{param:P[param]+h})
            minus=sample('minus',P|{param:P[param]-h})
        derivative=[(plus[key]-minus[key])/(2*h) for key in OBS]
        columns.append(derivative)
        stencils.append(dict(param=param,h=h,plus_switches=plus['switches'],
                             minus_switches=minus['switches'],derivatives=dict(zip(OBS,derivative))))
    J=np.array(columns).T
    rs=np.maximum(np.max(np.abs(J),axis=1),1e-12)
    cs=np.maximum(np.linalg.norm(J/rs[:,None],axis=0),1e-12)
    singular=np.linalg.svd((J/rs[:,None])/cs[None,:],compute_uv=False)
    relative=singular/singular[0]
    assert np.count_nonzero(J[OBS.index('spark')])>0
    assert rows[1]['incident']==0
    checks=3*len(rows)+2*len(NAMES)+2
    output=dict(status=f'{checks}/{checks} PASS',period=20*math.pi,
                measurements=OBS,parameters=NAMES,cases=rows,stencils=stencils,
                jacobian=J.tolist(),relative_singular_values=relative.tolist(),
                rank_relative_threshold_1e_5=int(np.sum(relative>1e-5)),
                spark_only_rank_upper_bound=1,
                caveat='Conditional synthetic model, approximate restored states, locally scaled Jacobian; no original device/ambient energy evidence.')
    print(json.dumps(output,indent=2))
if __name__=='__main__':main()
