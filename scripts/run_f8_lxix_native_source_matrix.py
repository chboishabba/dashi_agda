"""Run the actual native production propagation, with independent checkpoint per source.
Run repeatedly after exit 75; compare completed JSON outputs with the replay receipt.
No CI needed. No assertion of physical convergence.
"""
import argparse
import json
from pathlib import Path
import numpy as np
from ksw668_f8_tt_multipole import propagate

def main():
    p=argparse.ArgumentParser()
    p.add_argument('label',choices=('A0','A1','C0','C1'))
    p.add_argument('--work',type=Path,default=Path('.local-f8-lxix'))
    p.add_argument('--budget',type=float,default=12.)
    a=p.parse_args()
    a.work.mkdir(parents=True,exist_ok=True)
    try:
        result=propagate(dr=.008 if a.label[0]=='A' else .006,dy=.012,dt=.0012,
            eps=.04,final_t=12.,pulse=.065,inside_chord=.012,r_outer=3.01,y_outer=2.01,
            normal_order=3,conservative_source=True,weak_source_load=a.label[1]=='1',
            checkpoint=a.work/(a.label+'.npz'),budget=a.budget,checkpoint_every=16)
    except InterruptedError as e:
        print(e,flush=True)
        return 75
    assert result['steps']+1==2259 and result['weak_source_load']==(a.label[1]=='1')
    for prefix in ('receiver','far'):
        for kind in ('intrinsic_4D','projected_5D'):
            for suffix in ('','_tangent'):
                assert np.isfinite(result[prefix+'_mode_'+kind+'_electric_Weyl'+suffix]).all()
    path=a.work/(a.label+'.json')
    tmp=path.with_suffix('.tmp');tmp.write_text(json.dumps(result,indent=2)+'\n');tmp.replace(path)
    print(path,flush=True)
    return 0

if __name__=='__main__':
    raise SystemExit(main())
