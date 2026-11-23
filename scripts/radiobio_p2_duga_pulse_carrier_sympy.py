#!/usr/bin/env python3
"""Exact spectral negative control for Duga 'Woodpecker' radar.

Original/historical documentary leads: 1976 US Presidential Daily Brief
about Soviet over-the-horizon radar; contemporary HF radio monitoring.
DASHI independent illustrative signal algebra; it is not a digitisation
of the original radar waveform or a measured spectrum.
"""
import json
import sympy as S

def check():
    carrier, prf, modulation, time = S.symbols(
        'carrier prf modulation time', real=True)
    theta = 2*S.pi*carrier*time
    phi = 2*S.pi*prf*time
    # Three sinusoidal RF components; PRF is modulation, not LF carrier.
    wave = (1+modulation*S.cos(phi))*S.cos(theta)
    three = (S.cos(theta) +
             modulation/2*S.cos(theta+phi) +
             modulation/2*S.cos(theta-phi))
    assert S.simplify(S.expand_trig(wave-three)) == 0

    # Ideal square-law envelope detection exposes baseband repetition.
    detected = S.Rational(1,2)*(1+modulation*S.cos(phi))**2
    baseband = (S.Rational(1,2)+modulation**2/4 +
                modulation*S.cos(phi)+
                modulation**2/4*S.cos(2*phi))
    assert S.simplify(S.expand_trig(detected-baseband)) == 0

    illustrative_rf = S.Integer(10_000_000)
    repetition = S.Integer(10)
    assert 1/repetition == S.Rational(1,10)
    assert repetition != S.Rational(783,100)
    return {
      'status':'PASS',
      'tier':'SYNTHETIC_ALGEBRA_NOT_RECORDED_DUGA',
      'illustrative_carrier_hz':int(illustrative_rf),
      'example_repetition_hz':int(repetition),
      'sideband_hz':[int(illustrative_rf-repetition),
                     int(illustrative_rf), int(illustrative_rf+repetition)],
      'line_at_10_hz_in_transmitted_three_line_model':False,
      'ideal_envelope_detector_generates_10_hz':True,
      'repetition_period_s':'1/10',
      'repetition_not_schumann_7_83_hz':True,
      'physical_exceptions':'Actual keyed RF pulses contain additional HF sidebands, switching transients, and possible near-field components; no calibrated Earth/receiver LF emission is shown here.'
    }

if __name__ == '__main__':
    print(json.dumps(check(),indent=2,sort_keys=True))
