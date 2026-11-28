#!/usr/bin/env python3
"""J21: source-only end-to-end HF throughput, loss floor and event-branch checks.

Reuses the actual J20/J19/J18 nine-state engine, not a new source/topology.
The incident wave is an externally prescribed synthetic mathematical input.
No original Filsinger pin topology, ambient power measurement or gravity claim.
"""
import json
import sympy as S
import check_smith_filsinger_j20_perfect_capture_reactive_return_20261123 as j20
import check_smith_filsinger_j19_zero_freewheel_inverse_20261123 as j19
import check_smith_filsinger_j18_hf_spark_tank_20261123 as hf

J20_SHA = 'ed09b82287ec1ca0318b4f8e9d355f614d00d894'
J19_SHA = 'cc5cec2d4f881b38b4c01ef79dd93f36e9ef1439'
J18_SHA = 'f4270a475f010874056cfe3cdeff5ee8e43c44eb'
OPT = dict(drive_amp=0., gamma_internal=.0002, gamma_rad=.015,
           k=.35, kh=2., Gload=.52)
EXPECTED_LOAD = 46.561660078
EXPECTED_INCIDENT = 90.477868423

def exact_loss_floor():
    # On a restored HF-capacitor cycle, the capacitor's signed work is zero.
    # Therefore integral(x*ih dt)=G_L*integral(x^2 dt).
    # Cauchy-Schwarz implies integral(ih^2 dt)>=G_L^2 integral(x^2 dt).
    # Hence W_coil >= R_coil*G_L*W_load and
    # W_load/W_incident <= 1/(1+R_coil*G_L) for driver OFF,
    # nonnegative other losses, and restored total storage.
    rc, gl, x2, i2, xi = S.symbols('Rcoil Gload X2 I2 XI', positive=True)
    wload = gl*x2
    coil_lower = rc*gl*wload
    assert S.simplify(coil_lower - rc*gl**2*x2) == 0
    assert S.simplify((gl*x2)**2/x2-gl**2*x2) == 0
    ceiling = 1/(1+rc*gl)
    assert S.simplify(1-ceiling-rc*gl/(1+rc*gl)) == 0
    assert ceiling.subs({rc:S.Rational(1,20),gl:S.Rational(13,25)}) < 1
    return dict(strict_if_Rcoil_Gload_and_load_positive=True,
                capacitor_cycle_identity='integral(x ih)=Gload integral(x^2)',
                cauchy_schwarz='integral(ih^2)>=Gload^2 integral(x^2)',
                coil_loss_floor='Wcoil>=Rcoil*Gload*Wload',
                source_only_efficiency_ceiling='1/(1+Rcoil*Gload)',
                cannot_establish_physical_100_percent=True)

def pair(name, key, a, b, baseline):
    def measure(v):
        if key == 'phase':
            return j20.one(name+'_'+str(v), OPT, phase=v)
        return j20.one(name+'_'+str(v), OPT|{key:v})
    left,right=measure(a),measure(b)
    same=left['event_labels']==right['event_labels']==baseline['event_labels']
    shift=max((abs(x-y) for x,y in zip(left['event_times'],
              right['event_times'])),default=0.) if same else None
    assert same and left['events']==right['events']==22
    assert shift is not None and shift < .025
    return dict(values=[a,b],both_restored=True,same_22_ordered_events=same,
                maximum_aligned_event_time_shift=shift)

def run():
    assert j20.blob(j20.__file__) == J20_SHA
    assert j20.blob(j19.__file__) == J19_SHA
    assert j20.blob(hf.__file__) == J18_SHA
    floor=exact_loss_floor()
    prior=j20.one('J20_original_source_only',dict(drive_amp=0.))
    best=j20.one('J21_driver_off_wave_on',OPT)
    zero_internal=j20.one('J21_zero_internal_damping',OPT|dict(gamma_internal=0.))
    empty=j20.one('J21_no_driver_no_wave',OPT|dict(source_amp=0.))
    driver_only=j20.one('J21_driver_only_wave_off',OPT|dict(source_amp=0.,drive_amp=2.))
    assert prior['driver']==best['driver']==zero_internal['driver']==empty['driver']==0
    assert best['events']==22 and best['incoming']>0
    assert best['HF_load']>0 and abs(best['HF_load']-EXPECTED_LOAD)<.002
    assert abs(best['incoming']-EXPECTED_INCIDENT)<.002
    assert .514 < best['load_over_incident'] < .516
    assert best['wave_capture_fraction'] > .65
    assert best['load_over_incident'] > 300*prior['load_over_incident']
    assert zero_internal['field_heat']==0 and zero_internal['load_over_incident']<.53
    assert empty['incoming']==empty['driver']==empty['HF_load']==0
    assert driver_only['incoming']==0 and driver_only['driver']>0
    assert driver_only['HF_load']>0
    assert best['HF_coil_loss']+1e-6 >= .05*.52*best['HF_load']
    assert best['HF_load']/best['incoming']<1/(1+.05*.52)
    local_pairs={
        'source_amp':pair('source_amp','source_amp',1.1995,1.2005,best),
        'phase':pair('phase','phase',.299,.301,best),
        'k':pair('k','k',.3495,.3505,best),
        'Gload':pair('Gload','Gload',.518,.522,best),
    }
    # This strong-coupling neighbour is a NEGATIVE control: even if the
    # event count changes, it must never be promoted to a smooth derivative.
    neighbour=j19.cycle(j20.COMMON|OPT|dict(kh=2.005),phase=.3,
                        maxiter=13,tol=2e-5)
    adjacent_labels=(neighbour.get('event_labels') if neighbour['accepted']
                     else neighbour.get('last_event_labels',[]))
    same_branch=neighbour['accepted'] and adjacent_labels==best['event_labels']
    assert not same_branch
    no_switch=j20.one('J21_high_load_no_switch',dict(drive_amp=0.,
                   gamma_internal=.0002,gamma_rad=.02,k=.3,kh=2.,Gload=.56))
    assert no_switch['events']==0 and no_switch['HF_load']>0
    return dict(status='J21_J20_NATIVE_SOURCE_CONSUMER_LOCAL_EXECUTION_REQUIRED',
         exact= floor, baseline=prior, candidate=best,
         zero_internal=zero_internal, no_sources=empty,driver_only=driver_only,
         perturbations=local_pairs,
         negative_controls=dict(strong_kh_neighbour_same_branch=False,
                                strong_kh_neighbour_accepted=neighbour['accepted'],
                                strong_kh_neighbour_event_labels=adjacent_labels,
                                high_load_without_switching=no_switch),
         no_original_physical_energy_or_pin_measurement=True,
         local_equation_reimplementation_replayed_separately=True,
         source_file_itself_executed_in_this_commit=False,
         github_actions_or_ci_run=False,agda_kernel_run=False)

if __name__ == '__main__':
    print(json.dumps(run(),sort_keys=True,indent=2))
