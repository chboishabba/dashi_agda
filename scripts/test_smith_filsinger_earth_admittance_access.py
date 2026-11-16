#!/usr/bin/env python3
"""Source-bounded tests. Never treat model values as same-device measurements."""
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent))
from fractions import Fraction as F
from math import pi
import pytest
from check_smith_filsinger_earth_admittance_access import (
    DCColumn,J_BOROK_MEAN,vertical_near_surface_admittance,
    soil_pair_far_separated_resistance_ohm,required_soil_open_voltage_V,
    debye_admittance,debye_port_energy_rate,front_scale,scenario)

def test_exact_fixed_source_matching():
    src=DCColumn(250000,J_BOROK_MEAN,1)
    assert src.terminal_power_W(src.short_circuit_A/2)==pytest.approx(src.matched_load_W)
    for scale in (-1,0,.1,.3,1,2):
        assert src.terminal_power_W(scale*src.short_circuit_A)<=src.matched_load_W*(1+1e-12)

def test_full_column():
    s=scenario()['atmospheric_full_column']
    assert s['needed_area_0p4W_km2']==pytest.approx(2.71186440677966)
    assert s['needed_area_6p7W_km2']==pytest.approx(45.4237288135593)

def test_local_collection_not_ionosphere_short():
    s=scenario()['near_ground_2m_100Vm']
    assert s['Voc_V']==200
    assert s['needed_area_0p4W_km2']>3000

def test_soil_resistance_not_source_voltage():
    r=soil_pair_far_separated_resistance_ohm(100,.1)
    assert r==pytest.approx(100/(pi*.1))
    assert required_soil_open_voltage_V(100,.1,.4)==pytest.approx(22.56758334)

def test_dc_air_conductance():
    y=vertical_near_surface_admittance(100,2,1,J_BOROK_MEAN,0)
    assert y.real==pytest.approx(J_BOROK_MEAN/200)
    assert y.imag==0

def test_rf_displacement_not_real_replenishment():
    y=vertical_near_surface_admittance(100,2,1,J_BOROK_MEAN,7800)
    assert y.imag/y.real>1e7
    assert 200**2*y.real==pytest.approx(200*J_BOROK_MEAN)

def test_debye_positive_real():
    for f in (0,.01,1,7.83,7800,1e6):
        y=debye_admittance(f,1e-9,1e-12,[(2e-9,.003),(3e-9,.2)])
        assert y.real>=1e-9 and y.imag>=0

def test_exact_fraction_passive_dispersive_identity():
    v,vdot,x=F(7,3),F(-2,5),F(4,7)
    inp,udot,diss=debye_port_energy_rate(
        v,vdot,[x],F(1,5),F(2,9),[(F(2,3),F(3,4))])
    assert inp==udot+diss

def test_debye_empty_source_state():
    assert debye_port_energy_rate(0,0,[0],1,1,[(2,3)])==(0,0,0)

def test_wavefront_not_audio_clock():
    assert front_scale(7800,80000)>1
    assert front_scale(7.83,80000)<.02
    assert front_scale(7800,2)<.001

def test_soil_shape_sensitivity():
    assert soil_pair_far_separated_resistance_ohm(100,.2)<soil_pair_far_separated_resistance_ohm(100,.1)

def test_bad_parameters_fail_closed():
    with pytest.raises(ValueError): DCColumn(0,J_BOROK_MEAN,1)
    with pytest.raises(ValueError):
        vertical_near_surface_admittance(100,2,1,J_BOROK_MEAN,-1)
    with pytest.raises(ValueError):
        debye_port_energy_rate(1,1,[1],1,1,[])
