#!/usr/bin/env python3
"""Selected-model F10/F13 source-equivalent regressions. No physical admission."""
from math import isclose, pi
from dataclasses import replace
import pytest
from check_smith_filsinger_f10_f13_field_bridge import (
    f10_debye_modulation, f10_hall_pedersen, f10_poynting_local,
    f13_halfspace_laplace, f13_fixed_column, HalfSpaceCollector, run)


def test_f10_ade_parametric_work(): assert f10_debye_modulation()
def test_f10_hall_pedersen_neutral_frame(): assert f10_hall_pedersen()
def test_f10_boundary_poynting(): assert f10_poynting_local()
def test_f13_hemispherical_halfspace_pde(): assert f13_halfspace_laplace()
def test_f13_stratified_fixed_area_column(): assert f13_fixed_column()


@pytest.mark.parametrize('sigma,radius',[(1e-14,.1),(1e-14,1.),(3e-14,2.),(.1,10.)])
def test_exact_selected_hemisphere_current(sigma,radius):
    m=HalfSpaceCollector(sigma_air=sigma,radius_m=radius,potential_v=137.)
    assert isclose(m.conductance(),2*pi*sigma*radius)
    assert isclose(m.current(),m.potential_v/m.spread_resistance())
    assert isclose(m.ideal_disk_contact_g(),4*sigma*radius)

def test_different_electrode_shape_different_conductance():
    m=HalfSpaceCollector()
    assert m.conductance()!=m.ideal_disk_contact_g()

def test_conductivity_does_not_prove_natural_source_work():
    m=HalfSpaceCollector(potential_v=0.)
    assert m.current()==0.
    assert m.hypothetical_thevenin_matched_w(0.)==0.

def test_illustrative_voc_not_full_earth_ionosphere_potential():
    m=HalfSpaceCollector()
    assert m.hypothetical_thevenin_matched_w(200.)<1e-8
    assert m.spread_resistance()>1e12

def test_contract_limits_are_explicit():
    result=run()
    assert all(result['checks'].values())
    assert 'NOT exact' in result['F13_scope']
    assert 'NOT solved' in result['F10_scope']
