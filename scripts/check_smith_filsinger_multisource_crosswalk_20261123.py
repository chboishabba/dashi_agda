#!/usr/bin/env python3
"""Source-typed Duga / HAARP-SURA / Pais-YBCO crosswalk to native J12.

Consumes the ORIGINAL existing J12 switched coil/diode/spark port equations.
All native J12 values are dimensionless, synthetic and not source calibrated.
No radar, HAARP, superconducting or gravitational physical coupling is asserted.
Original external authors retain credit (see companion research audit).
"""
import json
import numpy as np
import sympy as S
from check_smith_filsinger_j12_restored_cycles_20261122 import BASE, advance

SOURCES = {
 'duga_radar_hf': dict(route='incident_HF_to_antenna_then_external_matching_to_J12',
  carrier='observed 16.39–16.57 MHz channels', envelope='10 Hz common pulse repetition',
  source='1985 Monitoring Times receiver observations', admission='calibrated HF E/H, antenna, rectifier/mixer and circuit port'),
 'haarp_electrojet_vlf': dict(route='HF_pump_to_D_region_electrojet_ELF_VLF_to_receiving_wave_port',
  carrier='3.25 MHz X-mode, historical 2005 experiment', envelope='575 and 2125 Hz modulation',
  source='Moore et al. 2007 DOI:10.1029/2006JA012063', admission='independent electrojet current and LF E/H, waveguide, receiver port'),
 'haarp_f_region': dict(route='HF_heater_to_F_region_magnetosonic_to_E_region_Hall_to_VLF',
  carrier='HF pump; frequency observation experiment-dependent', envelope='ELF/ULF generated current',
  source='2011 DOI:10.1029/2011GL049263', admission='separate plasma generator, damping, flux geometry and received field'),
 'sura_2026': dict(route='HF_pump_to_nonstationary_plasma_to_LH_whistler_to_receiving_wave_port',
  carrier='5.350 MHz O-mode', envelope='observed 8–9 and 17–18 kHz bands',
  source='Chernyshov et al. 2026 DOI:10.1029/2026GL123503', admission='nonlinear mode conversion, LAERT state, original E/B field and receiver port'),
 'pais_hfgwg': dict(route='independent_gravity_force_stress_observer_NOT_J12_electrical_wave',
  carrier='microwave/charged acoustic cavities, claimed', envelope='claimed high-frequency gravitational response',
  source='Pais US10322827B2 patent; JASON JSR-08-506 independent constraints', admission='independent gravity field/momentum test plus full EM/acoustic/thermal source ledger'),
 'ybco_gravity': dict(route='independent_gravimeter_NOT_J12_electrical_wave',
  carrier='superconductor DC/static/rotating/RF depending on experiment', envelope='gravity anomaly not reproducibly established',
  source='Li et al. Physica C 281 (1997); Hathaway et al. Physica C 385 (2003)', admission='calibrated gravimeter, RF/mechanical artifacts and controls')
}

def exact_source_gates():
    assert len(SOURCES)==6
    assert all(x['source'] and x['admission'] for x in SOURCES.values())
    assert SOURCES['pais_hfgwg']['route'].endswith('NOT_J12_electrical_wave')
    assert SOURCES['ybco_gravity']['route'].endswith('NOT_J12_electrical_wave')
    # A source frequency and a circuit-acoustic frequency are not interchangeable.
    f_audio=S.Integer(7800); f_sura_low=S.Interval(8000,9000)
    assert not f_sura_low.contains(f_audio)
    assert S.Integer(10)!=S.Rational(783,100)  # radar PRF is not Schumann 7.83 Hz
    # Identical receiver signals cannot identify four unknown complex gains.
    gains=S.symbols('g0:4'); signals=S.symbols('s0:4')
    signal=sum(g*s for g,s in zip(gains,signals))
    assert S.Matrix([signal]).jacobian(gains).rank()==1
    # A hypothetical four-channel independently metered measurement could
    # identify gains ONLY with known nonzero source stimuli and no aliasing.
    assert S.diag(*signals).det()==S.prod(signals)
    # Coherent channels interfere. Independent powers cannot simply be added
    # after merging waves into one physical port.
    a,b,phi=S.symbols('a b phi',real=True)
    w=a+b*S.exp(S.I*phi)
    mixed=S.simplify(S.expand_complex(w*S.conjugate(w)))
    assert S.simplify(mixed-(a*a+b*b+2*a*b*S.cos(phi)))==0
    assert S.simplify(S.integrate(mixed,(phi,0,2*S.pi))/(2*S.pi)-(a*a+b*b))==0
    return {'source_types':list(SOURCES),'generic_receiver_rank_vs_four_unknown_gains':'1/4',
        'full_four_meter_design_determinant':str(S.prod(signals)),
        'coherent_cross_work':'2*a*b*cos(phi)',
        'unknown_gain_and_source_clock_map':True,
        'actual_gravity_port_is_distinct_from_received_RF':True}

def native_j12_paid_work():
    # EXACT owner J12.advance with no change to its nonlinear state/energy
    # equations. This checks the input interface rather than claiming
    # physical map from Duga / HAARP spectral bands into J12 omega=1.1.
    zero=np.zeros(7)
    results={}
    for name,inc,amp in [('driver_only',False,0.),('unclassified_wave',True,.10)]:
        p=BASE|{'source_amp':amp}
        state,active,r=advance(p,inc,.25,zero,False,0.)
        assert len(state)==7 and all(np.isfinite(state))
        assert abs(r['residual'])<1e-6
        assert abs(r['incident']-r['outgoing']-r['net_wave'])<1e-8
        assert r['incident']==0 if not inc else r['incident']>0
        results[name]={k:r[k] for k in ('driver','incident','outgoing','net_wave',
             'spark','diode','heat','storage_delta','residual','switches')}
    # Explicit total sourced work ledger: source energy is not spark output.
    for name,r in results.items():
        assert abs(r['driver']+r['net_wave']-r['spark']-
          r['diode']-r['heat']-r['storage_delta'])<1e-6
    return results

def gravity_separate_and_clock_negative_controls():
    G,c,r,E=S.symbols('G c r E',positive=True)
    # Conditional Newtonian acceleration due to energy-as-gravitating-mass,
    # not a source-independent bound on gravity, pressure, waves or torsion.
    g=G*E/(c*c*r*r)
    assert S.simplify(g*r*r*c*c-G*E)==0
    # A measured magnetic/AC motor force requires reaction and field momentum;
    # it cannot be assigned to a free-standing gravity port.
    Fb,Fs,dPem,flux=S.symbols('Fb Fs dPem flux',real=True)
    force_balance=Fb+Fs+dPem+flux
    assert force_balance.subs({Fb:2,Fs:-3,dPem:1,flux:0})==0
    assert force_balance.subs({Fb:2,Fs:0,dPem:0,flux:0})!=0
    return {'gravity_channel_calibrated':False,'separate_force_closure':'F_body + F_source + dP_EM/dt + field_momentum_flux = 0',
      'conditional_point_energy_acceleration':'G*E/(c^2*r^2)',
      'source_clocks_mapped_to_J12_dimensionless_omega':False,
      'real_superconducting_GW_source_observed':False}

def run():
    return {'status':'PASS','scope':'EXACT_SYMBOLIC_AND_NATIVE_J12_SYNTHETIC_SOURCE_INTERFACE',
       'source_admission':exact_source_gates(),
       'original_j12_nonlin_circuit':native_j12_paid_work(),
       'gravity_force_channel':gravity_separate_and_clock_negative_controls(),
       'proven_same_apparatus_frequency_or_received_watts':False,
       'agda_kernel_verified':False,'original_RF_or_gravimeter_data_replayed':False}

if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
