#!/usr/bin/env python3
"""Source-constrained illustrative Duga four-window HF gate.
Historic observer: Monitoring Times, August 1985, Woodpecker investigation.
Original Soviet participant: Aleksandr Babakin, Feb 1991; translation JPRS-UMA-91-012.
Not a digitised waveform, original spectrum, or physiological transfer.
"""
import json
import sympy as S
T = S.Rational(1, 10)
WINDOW = S.Rational(7,1000)
PULSE = S.Rational(4,1000)  # illustrative inside reported 3--6ms range
STARTS = tuple(i*WINDOW for i in range(4))
FREQUENCIES_KHZ=(16450,16490,16570,16390)

def coefficient(start, n):
    if n == 0: return PULSE/T
    return S.sin(S.pi*n*PULSE/T)/(S.pi*n) * S.exp(-2*S.pi*S.I*n*(start+PULSE/2)/T)

def verify():
    assert all(STARTS[i]+WINDOW<=STARTS[i+1] for i in range(3))
    assert STARTS[3]+WINDOW==S.Rational(28,1000)
    assert T-(STARTS[3]+WINDOW)==S.Rational(72,1000)
    assert all(STARTS[i]+PULSE<=STARTS[i]+WINDOW for i in range(4))
    assert PULSE/T==S.Rational(1,25)
    assert 4*PULSE/T==S.Rational(4,25)
    assert coefficient(STARTS[0],0)==S.Rational(1,25)
    expected=(S.sin(S.pi/25)/S.pi)**2
    assert S.simplify(S.expand_complex(coefficient(STARTS[0],1)*S.conjugate(coefficient(STARTS[0],1)))-expected)==0
    # Four different HF frequencies, one associated with each time window.
    assert len(set(FREQUENCIES_KHZ))==4
    assert min(FREQUENCIES_KHZ)>1000
    # Six-second shifts repeated four times form a 24-s assignment cycle.
    rotations=[tuple(FREQUENCIES_KHZ[(i+j)%4] for i in range(4)) for j in range(4)]
    assert len(set(rotations))==4 and rotations[0]==rotations[4%4]
    assert sum(1 for i in range(4) for j in range(4) if rotations[i][j]==FREQUENCIES_KHZ[0])==4
    return {'status':'PASS','source':'1985 contemporary Monitoring Times oscilloscope description','physical_evidence':'not recreated from raw original waveform',
            'repetition_hz':10,'window_ms':7,'windows_per_frame':4,'silent_ms':72,'illustrative_pulse_ms':4,
            'duty_fraction_each_carrier':str(PULSE/T),'duty_fraction_all_four':str(4*PULSE/T),
            'original_reported_static_carrier_khz':list(FREQUENCIES_KHZ),'model_cyclic_assignment_s':24,
            'baseband_harmonic_spacing_hz':10,'single_carrier_dc_envelope_fourier_coefficient':str(coefficient(STARTS[0],0)),
            'first_envelope_sideband_power_coefficient_squared':str(expected),
            'physical_warning':'Each modulated carrier has RF sidebands; any LF signal at detector is not evidence for an independently radiated 10-Hz carrier.'}
if __name__=='__main__':print(json.dumps(verify(),indent=2))
