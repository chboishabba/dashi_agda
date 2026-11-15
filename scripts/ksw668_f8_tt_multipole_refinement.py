#!/usr/bin/env python3
"""F8 ORIGINAL a=t compact TT l=0,2,4 three-grid full gate (fail closed).

Runs three simultaneous physically identical source/receiver t=12 cases
and distinct dy, dr, dt. Requires convergence of SAME receiving event
and a negligible field at an event outside the entire BULK causal future
of the spatial source. Finite-volume source uses analytically integrated
radial compact TT multipole forcing. No empirical assertion.

Expected runtime may exceed tool timeout: run locally on pinned repo.
"""
import json
import math
from pathlib import Path
from ksw668_f8_tt_multipole import propagate

def audit():
    grids=((.012,.016,.0025),(.008,.012,.0018),(.006,.011,.00135))
    common=dict(eps=.04,final_t=12.,pulse=.065,inside_chord=.012,
       r_outer=3.15,y_outer=2.6,conservative_source=True)
    rows=[propagate(dr=dr,dy=dy,dt=dt,**common) for dr,dy,dt in grids]
    key='retarded_TT_yy_scaled_by_eps4'
    fields=[r[key] for r in rows]
    outside=[r['far_TT_yy_scaled_by_eps4'] for r in rows]
    radius=[r['receiver_grid_r'] for r in rows]
    assert max(radius)-min(radius)<1e-12
    assert all(r['discrete_support_photon_margin']>0 for r in rows)
    last=abs(fields[-1]-fields[-2])/max(abs(fields[-1]),1e-30)
    far_ratio=abs(outside[-1])/max(abs(fields[-1]),1e-30)
    sign_stable=(fields[0]*fields[1]>0 and fields[1]*fields[2]>0)
    # These are provisional *numerical* thresholds, not a mathematical
    # or experimentally calibrated error certificate.
    numerical_gate=last<.01 and far_ratio<1e-4 and sign_stable
    return dict(model='original moving AdS5 a=t Neumann with compact TT',
        same_physical_receiver_across_three_grids=True,rows=rows,
        relative_last_pair_drift=last,
        far_over_early_last_ratio=far_ratio,
        source_sign_stable=sign_stable,
        provisional_field_only_numeric_gate=numerical_gate,
        full_B4_converged=False,
        both_Weyl_computed=False,
        formal_error_bound_provided=False,
        physical_graviton_observed=False,
        next_gates=['independently controlled dy/dt vs dr refinement',
                    'moving brane tensor source-to-Weyl extraction',
                    'physically certified causal outside-bulk control',
                    'formal source and continuum Agda acceptance'])

if __name__=='__main__':
    data=audit()
    receipt=Path(__file__).with_name('ksw668_f8_tt_multipole_refinement_receipt.json')
    receipt.write_text(json.dumps(data,indent=2)+'\n',encoding='utf8')
    print(json.dumps({k:v for k,v in data.items() if k not in ('rows',)},indent=2))
    if not data['provisional_field_only_numeric_gate']:
        print('OPEN: compact TT three-grid field and outside-cone acceptance not met')
        raise SystemExit(42)
    print('Field-only provisional numeric threshold met; both-Weyl/Agda/physical gates still OPEN')
