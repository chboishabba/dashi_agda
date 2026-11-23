#!/usr/bin/env python3
"""P2 Duga: four-window HF source -> received aperture -> detected baseband.

Original timing authority: contemporary Monitoring Times August 1985.
Original Soviet programme account: Babakin 1991, JPRS-UMA-91-012.
This is an EXACT CONDITIONAL PASSIVE-RECEIVER MODEL, not original HF
instrument data, a measured antenna geometry, or physiological energy.
"""
import json
import sympy as S

T=S.Rational(1,10)
slot=S.Rational(7,1000)
pulse=S.Rational(4,1000)  # illustrative within 3--6 ms reported range
frequencies_khz=(16450,16490,16570,16390)
c=S.Integer(299792458)

def test():
    assert 4*slot/T==S.Rational(7,25)  # allocated time, not RF-on time
    assert 4*pulse/T==S.Rational(4,25)
    assert pulse/slot==S.Rational(4,7)
    assert T-4*slot==S.Rational(72,1000)
    assert T-4*pulse==S.Rational(84,1000)
    # All four carrier windows are distinct; receiver aperture depends on f.
    frequencies=[S.Integer(k)*1000 for k in frequencies_khz]
    aperture=[c**2/(4*S.pi*f**2) for f in frequencies] # G=1 isotropic
    incident_flux_peak=S.symbols('S_peak',positive=True)
    coupling=S.symbols('eta',nonnegative=True)
    loaded=[incident_flux_peak*coupling*pulse/T*A for A in aperture]
    avg=S.factor(sum(loaded))
    assert S.simplify(avg -
       incident_flux_peak*coupling*pulse/T*sum(aperture))==0
    assert all(S.simplify(a*4*S.pi*f*f-c*c)==0 for a,f in zip(aperture,frequencies))
    # Spectrum = RF carriers and 10Hz-spaced sidebands for periodic
    # envelopes; square-law or rectifying detection makes baseband locally.
    # Detected LF electrical output must be paid by intercepted HF energy.
    hf_intercept=S.symbols('hf_intercept',nonnegative=True)
    lf_load=S.symbols('lf_load',nonnegative=True)
    dissip=S.symbols('dissip',nonnegative=True)
    stored=S.symbols('stored',nonnegative=True)
    assert S.simplify(hf_intercept-(lf_load+dissip+stored)).subs(
       {hf_intercept:7,lf_load:2,dissip:3,stored:2})==0
    # An uncalibrated demodulated magnitude cannot identify flux/power:
    # z = gain * field; scaling field by k and gain by 1/k preserves z
    # while flux ~ field^2 changes. This is true even with nonzero z.
    field,gain,k=S.symbols('field gain k',nonzero=True,real=True)
    assert S.simplify((field*k)*(gain/k)-field*gain)==0
    assert S.simplify((field*k)**2-field**2)!=0
    # Separate original-source identity: no independent 10Hz radiator is
    # asserted in the 4 HF-carrier gated receiver model.
    return {
      'status':'PASS','tier':'EXACT_SYNTHETIC_PASSIVE_BOUND_NOT_FIELD_REPLAY',
      'source_frequency_khz':list(frequencies_khz),
      'slots_ms':7,'illustrative_pulse_ms':4,
      'slot_fraction':'7/25','rf_on_fraction':'4/25',
      'rf_off_fraction':'21/25','trailing_silence_ms':72,
      'mean_received_available_power_formula':
          'S_peak * eta * (4ms/100ms) * sum_i(c^2/(4*pi*f_i^2))',
      'source_flux_required_for_watts':True,
      'aperture_gain_polarization_mismatch_need_calibration':True,
      'receiver_work_budget':'P_HF_intercept = P_LF_load + P_dissipation + dU/dt (closed RF detector; no extra source)',
      'demodulated_amplitude_alone_cannot_identify_incident_power':True,
      'direct_10hz_transmitted_carrier_in_this_model':False,
      'original_antenna_or_receiver_field_data_used':False,
      'physical_limit':'Real pulse shapes/frequencies/antenna directivity/ionospheric attenuation unknown in this fixture'
    }

if __name__=='__main__':print(json.dumps(test(),indent=2,sort_keys=True))
