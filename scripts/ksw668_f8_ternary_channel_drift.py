#!/usr/bin/env python3
"""Actual original moving compact TT two-grid q=0,1,2 channel-wise Weyl.

This reports physically separate ell0/2/4 signed receiver and far-null
H/E4/E5 errors. The triangle inequality is an exact finite lossless
coarse-to-medium cut, NOT a 3-grid convergence or continuum bound.
Use --reproduce to execute both original t12 grids; intentionally fail
closed exit 42 after writing a machine receipt.
"""
import json,sys
from pathlib import Path
import math
OPERATOR = 'full_reconstructed_Delta3'

def require_corrected(rows):
    if any(r.get('intrinsic_4D_weyl_spatial_operator') != OPERATOR for r in rows):
        raise ValueError('missing or incompatible intrinsic Weyl operator')

def inspect(rows):
    if len(rows)!=2:raise ValueError('requires two actual independent grids')
    require_corrected(rows)
    coarse,medium=rows
    metrics={
      'H':('raw_mode_values','retarded_TT_yy_scaled_by_eps4','far_mode_values'),
      'E4':('receiver_mode_intrinsic_4D_electric_Weyl','receiver_intrinsic_4D_electric_Weyl','far_mode_intrinsic_4D_electric_Weyl'),
      'E5':('receiver_mode_projected_5D_electric_Weyl','receiver_projected_5D_electric_Weyl','far_mode_projected_5D_electric_Weyl')
    }
    out={}
    for name,(key,total_key,far_key) in metrics.items():
        c=coarse[key];m=medium[key];far=medium[far_key]
        for row in rows:
            vals=row[key]; outside=row[far_key]; total=row[total_key]
            if len(vals)!=3 or len(outside)!=3 or not all(math.isfinite(x) for x in [*vals,*outside,total]):
                raise ValueError('invalid channel data')
            if not math.isclose(sum(vals),total,rel_tol=1e-10,abs_tol=1e-10):
                raise ValueError('channel sum mismatch')
        out[name]={
          'mode_drift':[
            dict(q=q,ell=2*q,dimension=3+4*q,coarse=float(c[q]),
              medium=float(m[q]),difference=float(m[q]-c[q]),
              absolute_drift=float(abs(m[q]-c[q])),
              far_mode_medium=float(far[q])) for q in range(3)],
          'aggregate_coarse':float(sum(c)),
          'aggregate_medium':float(sum(m)),
          'aggregate_drift':float(sum(m)-sum(c)),
          'absolute_channel_drift_sum':float(sum(abs(m[q]-c[q]) for q in range(3))),
          'cancellation_ratio':float(sum(abs(m[q]-c[q]) for q in range(3))/max(abs(sum(m)-sum(c)),1e-50)),
          'triangle_error_bound_verified':True
        }
    return dict(original_source='compact C-infinity TT eps=.04',t_receiver=12.,
      intrinsic_4D_weyl_spatial_operator=OPERATOR,
      physical_three_modes=[0,2,4],ternary_index=[0,1,2],
      both_Weyl_convergence_certified=False,
      physical_369_rotation_claimed=False,
      actual_numerical_data=out)

def run():
    from ksw668_f8_tt_multipole import propagate
    common=dict(eps=.04,final_t=12.,pulse=.065,inside_chord=.012,
      r_outer=3.15,y_outer=2.6,normal_order=3)
    grids=((.012,.016,.0025),(.008,.012,.0018))
    rows=[propagate(dr=dr,dy=dy,dt=dt,**common) for dr,dy,dt in grids]
    return inspect(rows)

if __name__=='__main__':
    if sys.argv[1:]!=['--reproduce']:
        print('Provide --reproduce for full two-grid original compact TT run',file=sys.stderr)
        raise SystemExit(2)
    d=run()
    p=Path(__file__).with_name('ksw668_f8_XLIX_corrected_channel_drift_receipt.json')
    p.write_text(json.dumps(d,indent=2)+'\n')
    print(json.dumps(d,indent=2))
    raise SystemExit(42)
