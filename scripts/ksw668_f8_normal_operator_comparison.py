#!/usr/bin/env python3
"""KSW original moving a=t compact TT: three normal stencils, TWO-grid comparator.

normal_order=2: legacy second-order one-sided, boundary energy no-go;
normal_order=1: first-order energy-SBP and forced SSPRK3 normal-only bound;
normal_order=3: second-order interior SBP2-SAT weak Israel boundary.
Numerical source and receiver remain original t12 compact TT. A TWO-grid
comparator never certifies nonzero receiver/Weyl or early graviton.
Run --reproduce for actual full original moving PDE two-grid runs;
the failed numerical gate deliberately exits 42.
"""
import json,sys
from pathlib import Path
def diagnostics(rows):
    keys=('retarded_TT_yy_scaled_by_eps4',
          'receiver_intrinsic_4D_electric_Weyl',
          'receiver_projected_5D_electric_Weyl')
    fars=('far_TT_yy_scaled_by_eps4',
          'far_intrinsic_4D_electric_Weyl',
          'far_projected_5D_electric_Weyl')
    out={}
    for key,far in zip(keys,fars):
        x,y=[row[key] for row in rows]
        out[key]=dict(coarse=x,medium=y,
            relative_drift_vs_medium=abs(y-x)/max(abs(y),1e-30),
            far_medium=rows[-1][far],
            far_to_receiver_medium=abs(rows[-1][far])/max(abs(y),1e-30))
    out['only_two_grids']=True
    out['receiver_both_Weyl_convergence_accepted']=False
    out['empirical_graviton_observed']=False
    return out
def reproduce():
    from ksw668_f8_tt_multipole import propagate
    grids=((.012,.016,.0025),(.008,.012,.0018))
    common=dict(eps=.04,final_t=12.,pulse=.065,inside_chord=.012,
       r_outer=3.15,y_outer=2.6,conservative_source=True)
    rows={normal:[propagate(dr=dr,dy=dy,dt=dt,
                 normal_order=normal,**common) for dr,dy,dt in grids]
          for normal in (2,1,3)}
    return dict(scheme_metrics={str(k):diagnostics(v) for k,v in rows.items()},
       source='actual original moving t12 compact TT PDE',
       full_numerical_convergence_certified=False)
if __name__=='__main__':
    if sys.argv[1:]!=['--reproduce']:
        print('Use --reproduce to run the expensive two-grid comparison',file=sys.stderr)
        raise SystemExit(2)
    d=reproduce()
    p=Path(__file__).with_name('ksw668_f8_normal_operator_comparison_receipt.json')
    p.write_text(json.dumps(d,indent=2)+'\n')
    print(json.dumps(d,indent=2))
    print('OPEN: 2 grids cannot certify both Weyl or physical reception')
    raise SystemExit(42)
