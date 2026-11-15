#!/usr/bin/env python3
"""F8 actual original a=t compact TT t12 weighted SBP2 SAT normal_order4.
Two-grid replay for H, intrinsic E4 and projected E5, with ORIGINAL
photon-dark receiver and an outside-bulk-cone null control. Two grids
are explicitly NON-ACCEPTANCE; exit 42 after recording numerical data.
"""
import json
from pathlib import Path
from ksw668_f8_tt_multipole import propagate

def audit():
    grids=((.012,.016,.0025),(.008,.012,.0018))
    common=dict(eps=.04,final_t=12.,pulse=.065,inside_chord=.012,
       r_outer=3.15,y_outer=2.6,conservative_source=True,normal_order=4)
    rows=[propagate(dr=dr,dy=dy,dt=dt,**common) for dr,dy,dt in grids]
    assert rows[0]['receiver_grid_r']==rows[1]['receiver_grid_r']
    assert all(r['discrete_support_photon_margin']>0 for r in rows)
    assert all(r['weighted_original_AdS_SBP2SAT_full_semidiscrete_contract'] for r in rows)
    out={}
    for label,key,far in (
        ('tensor_Hyy','retarded_TT_yy_scaled_by_eps4','far_TT_yy_scaled_by_eps4'),
        ('intrinsic_4D_Weyl','receiver_intrinsic_4D_electric_Weyl','far_intrinsic_4D_electric_Weyl'),
        ('projected_5D_Weyl','receiver_projected_5D_electric_Weyl','far_projected_5D_electric_Weyl')
    ):
        x,y=[r[key] for r in rows]
        out[label]=dict(coarse=x,medium=y,
            medium_relative_drift=abs(y-x)/max(abs(y),1e-30),
            medium_far_control=rows[-1][far],
            medium_far_relative_to_receiver=abs(rows[-1][far])/max(abs(y),1e-30))
    return dict(scheme='AdS5 weighted-split SBP2 SAT original Israel, normal_order=4',
        original_a_t=True,receiver_t=12,spatial_TT_compact=True,
        actual_original_source_photon_dark=True,
        actual_grid_count=2,metrics=out,
        original_full_coupled_semidiscrete_energy_math_closed=True,
        original_full_coupled_SSPRK3_RK_energy_closed=False,
        both_Weyl_threegrid_convergence=False,
        experimentally_observed_graviton=False)
if __name__=='__main__':
    result=audit()
    output=Path(__file__).with_name('ksw668_f8_weighted_SBP4_two_grid_receipt.json')
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))
    raise SystemExit(42)
