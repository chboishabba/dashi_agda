#!/usr/bin/env python3
"""Conditional physical Earth/ionosphere source-access and dipole scales.
Do not infer device geometry, total accessible energy, or true Earth work."""
from math import pi
EPS0=8.8541878128e-12
C0=299792458.
EARTH_R=6371000.
H=80000.
V=250000.
J=2e-12
def column_source(power_w,area_m2=1):
    return dict(global_full_column_W_per_m2=V*J,
        area_required_m2=power_w/(V*J),
        redirect_factor_relative_to_area=power_w/(V*J*area_m2))
def spherical_vacuum_C():
    return 4*pi*EPS0*EARTH_R*(EARTH_R+H)/H
def open_short_dipole_radres(f_hz,length_m):
    return 20*pi*pi*(f_hz*length_m/C0)**2
def check():
    assert abs(column_source(.4)['area_required_m2']-800000)<1e-7
    assert abs(column_source(6.7)['area_required_m2']-13400000)<1e-6
    assert abs(column_source(1000)['area_required_m2']-2e9)<1
    assert .05<spherical_vacuum_C()<.06
    assert 0.5*0.7*V*V>2e10  # literature effective GEC capacitor, not vacuum shell
    assert open_short_dipole_radres(7.83,2)<1e-12
    assert open_short_dipole_radres(7800.,2)<1e-6
    print('PASS global circuit full-column *conditional* throughput and small dipole bounds')
if __name__=='__main__':check()
