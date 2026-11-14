#!/usr/bin/env python3
"""Conditional Tesla-tower emission max-cut, not a Wardenclyffe reconstruction.

All drive powers, mode couplings and geometry approximations are hypothetical.
The Schumann cavity is reduced to an energy-equivalent, uniform-volume model,
not solved Maxwell PDEs with actual Earth-ionosphere boundary conditions.
"""
from fractions import Fraction
from math import cos, isclose, pi, sqrt

C = 299792458.0
EPS0 = 8.8541878128e-12
Z0 = 376.730313668
R_EARTH = 6371000.0

def short_monopole_resistance(height_m, frequency_hz):
    """Ideal ground, electrically short triangular-current monopole only."""
    return 40*pi*pi*(height_m*frequency_hz/C)**2

def ideal_free_space_farfield(power_radiated_w, range_m):
    return sqrt(Z0*power_radiated_w/(4*pi*range_m**2))

def linear_am_spectrum(carrier_hz, modulator_hz, depth=Fraction(1,2)):
    """Positive cosine frequencies from a LINEAR AM waveform."""
    assert carrier_hz > modulator_hz > 0
    return {carrier_hz-modulator_hz: depth/2,
            carrier_hz: Fraction(1), carrier_hz+modulator_hz: depth/2}

def cavity_mode_budget(input_w=1e6, coupling=0.01, q=5.0,
                       frequency_hz=7.83, effective_height_m=80000.0,
                       receiver_amplitude_transfer=1.0):
    """Conditional lumped mode energy. Not a prediction at a brain."""
    assert input_w >= 0 and 0 <= coupling <= 1 and q > 0
    assert 0 <= receiver_amplitude_transfer <= 1
    assert frequency_hz > 0 and effective_height_m > 0
    omega = 2*pi*frequency_hz
    volume = 4*pi*R_EARTH**2*effective_height_m
    p_mode = input_w*coupling
    u_joules = p_mode*q/omega
    # Assumes equally divided average electric and magnetic mode energy:
    # U_e=U/2=(epsilon/2)*V*E_rms^2.
    e_characteristic = sqrt(u_joules/(EPS0*volume))
    return dict(mode_power_w=p_mode, stored_energy_j=u_joules,
                equivalent_volume_m3=volume,
                characteristic_field_rms_v_m=e_characteristic,
                toy_received_field_rms_v_m=e_characteristic*receiver_amplitude_transfer)

def driven_mode_magnitude(f0_hz, quality, drive_hz):
    """Undimensioned damped-oscillator response, not actual Schumann overlap."""
    assert f0_hz > 0 and quality > 0 and drive_hz >= 0
    x=drive_hz/f0_hz
    return 1/sqrt((1-x*x)**2+(x/quality)**2)

def free_ringdown_times(f0_hz, quality):
    """Single-mode linear energy and amplitude e-fold times in seconds."""
    assert f0_hz > 0 and quality > 0
    energy=quality/(2*pi*f0_hz)
    return {"energy_s":energy,"amplitude_s":2*energy,"linewidth_hz":f0_hz/quality}

def test():
    # Frequency non-promotion: an 8Hz envelope is not a radiated 8Hz line.
    spectrum = linear_am_spectrum(100000, 8)
    assert spectrum == {99992: Fraction(1,4),
                        100000: Fraction(1), 100008: Fraction(1,4)}
    assert 8 not in spectrum
    for t in (0.0, 0.000001, 0.000127, 0.0123, 0.334):
        wave=(1+0.5*cos(2*pi*8*t))*cos(2*pi*100000*t)
        expanded=sum(float(amp)*cos(2*pi*f*t) for f,amp in spectrum.items())
        assert isclose(wave,expanded,abs_tol=1e-7,rel_tol=1e-7)
    assert isclose(short_monopole_resistance(57,7.83), 8.75e-10,rel_tol=.005)
    assert isclose(ideal_free_space_farfield(1e5,1e5), 0.017313,rel_tol=.001)
    a=cavity_mode_budget()
    assert isclose(a["characteristic_field_rms_v_m"],.00167719,rel_tol=.001)
    b=cavity_mode_budget(coupling=.04)
    assert isclose(b["characteristic_field_rms_v_m"],2*a["characteristic_field_rms_v_m"])
    assert cavity_mode_budget(coupling=0)["toy_received_field_rms_v_m"] == 0
    assert cavity_mode_budget(receiver_amplitude_transfer=0)["toy_received_field_rms_v_m"] == 0
    assert isclose(a["mode_power_w"],
                   a["stored_energy_j"]*2*pi*7.83/5.0)
    rd=free_ringdown_times(7.83,5)
    assert isclose(rd["energy_s"],.10163,rel_tol=.001)
    assert isclose(rd["amplitude_s"],.20325,rel_tol=.001)
    assert isclose(rd["linewidth_hz"],1.566,rel_tol=.001)
    assert isclose(driven_mode_magnitude(7.83,5,7.83),5.0,rel_tol=1e-12)
    assert driven_mode_magnitude(7.83,5,6.0)<5.0
    return a

if __name__ == "__main__":
    result=test()
    print("PASS: linear AM sidebands, non-identifiability, monopole and mode budgets")
    print(result)
    print("NOT VALIDATED: historical drive, physical Earth-mode overlap, receiver transfer")
