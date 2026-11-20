#!/usr/bin/env python3
"""Original a=t AdS5 TT: reproducible three-grid H/E4/E5 fail-closed audit.

Replays use SAME compact C-infinity 3D TT eps=.04, Poincare pulse=.065,
physical t12 receiver, unweighted weak-Israel SAT mode3. Parallel Numba
runs three independent even multipoles without changing their equations.
Causal box r_outer=3.01, y_outer=2.01 has radial reach >Tspan, and any
normal wall reflection-to-receiver needs >Tspan. This has been checked
against the historical larger box on coarse and medium receivers.
The signed q=0/1/2, both Weyl, and far controls are never aggregated
before testing. No Richardson error from non-geometric mesh sequences.
"""
import argparse,json
from pathlib import Path

REPO=Path(__file__).resolve().parents[1]
RECEIPT=REPO/'Artifacts/ksw668/ads5_f8_threegrid_per_channel_radial_normal_factorial_maxcut_xi_20261116.json'
GRID={
 'coarse':(.012,.016,.0025),'medium':(.008,.012,.0018),
 'fine':(.006,.009,.0012),
 'factorial-A':(.008,.012,.0012),'factorial-B':(.008,.009,.0012),
 'factorial-C':(.006,.012,.0012),'factorial-D':(.006,.009,.0012),
 'medium-dt-half':(.008,.012,.0009),'fine-dt-half':(.006,.009,.0006)
}
def verify():
    # Historical receipt only; never reinterpret as corrected E4.
    # Availability depends on the historical artifact being present.
    d=json.loads(RECEIPT.read_text())
    assert not d['closure']['three_grid_original_E4_E5_acceptance']
    assert not d['closure']['pointwise_H4epsilon_to_Weyl']
    assert d['finite_box']['radial_oneway_min_from_source']>d['finite_box']['source_to_receiver_available_Poincare_span']
    assert d['finite_box']['normal_boundary_reflected_path_lower_bound']>d['finite_box']['source_to_receiver_available_Poincare_span']
    for name in ('H','E4','E5'):
        rows=d['per_harmonic_signed_spatial_refinement'][name]
        assert [r['ell'] for r in rows]==[0,2,4]
        for i in range(3):
            x=rows[i]
            assert abs((x['fine']-x['medium'])-x['fine_minus_medium'])<1e-12
        assert all(abs(x['fine_minus_medium'])>abs(x['medium_minus_coarse']) for x in rows)
    for name in ('E4','E5'):
        rows=d['fixed_dt_radial_normal_factorial']['signed_modewise'][name]
        for r in rows:
            assert abs(r['radial_change']+r['normal_change']+r['interaction']-r['total_change'])<1e-12
        assert abs(rows[0]['radial_fraction_of_signed_total'])>.95
    assert d['finite_SBP2_boundary_Udot_only_repair_no_go']['independent_weak_Israel_wall_and_far_source_generically_incompatible']
    return d

def replay_grid(label,checkpoint=None,budget=75.,checkpoint_every=8):
    if label not in GRID:raise ValueError('choose one named original mesh')
    from ksw668_f8_tt_multipole import propagate
    dr,dy,dt=GRID[label]
    result=propagate(dr=dr,dy=dy,dt=dt,eps=.04,final_t=12.,
        pulse=.065,inside_chord=.012,r_outer=3.01,y_outer=2.01,
        normal_order=3,conservative_source=True,checkpoint=checkpoint,budget=budget,checkpoint_every=checkpoint_every)
    from ksw668_f8_ternary_channel_drift import require_corrected
    require_corrected([result])
    keys=('intrinsic_4D_weyl_spatial_operator','step_radial','step_bulk','step_time','raw_mode_values',
        'receiver_mode_intrinsic_4D_electric_Weyl',
        'receiver_mode_projected_5D_electric_Weyl',
        'receiver_mode_intrinsic_4D_electric_Weyl_tangent',
        'receiver_mode_projected_5D_electric_Weyl_tangent',
        'far_mode_intrinsic_4D_electric_Weyl',
        'far_mode_projected_5D_electric_Weyl',
        'discrete_support_photon_margin')
    # Preserve the complete original receiver and geometry receipt so downstream
    # signed comparisons do not lose axial controls, tangent or aggregate data.
    for k in keys:
        if k not in result: raise ValueError('missing required receiver field: '+k)
    report=dict(result)
    report['requested_mesh']={'dr':dr,'dy':dy,'dt':dt}
    report['receiver_receipt_schema']='XLIX-full-spatial-v2'
    report.update(grid=label,physical_early_Weyl_acceptance=False,
        same_original_adS5_model=True)
    outfile=REPO/'Artifacts/ksw668'/('ads5_f8_XLIX_corrected_replay_'+label+'.json')
    outfile.parent.mkdir(parents=True,exist_ok=True)
    outfile.write_text(json.dumps(report,indent=2)+'\n')
    return outfile

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('--run-grid',choices=tuple(GRID))
    ap.add_argument('--accept',action='store_true',help='fail closed for physical Weyl convergence')
    ap.add_argument('--checkpoint',type=Path)
    ap.add_argument('--budget',type=float,default=75.)
    ap.add_argument('--checkpoint-every',type=int,default=8)
    args=ap.parse_args()
    if args.budget<=0 or args.checkpoint_every<=0:ap.error('positive budget and checkpoint interval required')
    if args.run_grid:
        try:print('Completed numerical mesh only:',replay_grid(args.run_grid,args.checkpoint,args.budget,args.checkpoint_every))
        except InterruptedError as exc:
            print(str(exc));raise SystemExit(75)
    else:print('Historical LEGACY AXIAL negative receipt checked:',verify()['schema'])
    if args.accept:raise SystemExit(42)
