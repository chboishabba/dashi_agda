#!/usr/bin/env python3
"""Exact rational F10 four-direction finite space-time Stokes/Poynting.

Deliberately FINITE arithmetic, not a Maxwell PDE, conductor calibration,
Yee numerical stability or a physical solar-harvesting demonstration.
"""
from fractions import Fraction as Q
from random import Random
import pytest

def partial(samples):
    """The exact original Ward partial forward difference."""
    return sum((samples[k+1]-samples[k] for k in range(len(samples)-1)),Q(0))

def space_time_balance(energy,x,y,z,loss,load,natural,controller):
    dt=partial(energy)
    faces=partial(x)+partial(y)+partial(z)
    endpoint=(energy[-1]-energy[0]) + ((x[-1]-x[0])+
              (y[-1]-y[0])+(z[-1]-z[0]))
    local=dt+faces
    assert local==endpoint
    return local+loss+load==natural+controller

def genuine_window(seed):
    r=Random(seed)
    seq=lambda n:[Q(r.randrange(-500,501),r.randrange(1,20)) for _ in range(n)]
    e,x,y,z=(seq(r.randrange(2,11)) for _ in range(4))
    loss=Q(r.randrange(1,99),r.randrange(1,10))
    load=Q(r.randrange(1,99),r.randrange(1,10))
    control=Q(r.randrange(-100,101),r.randrange(1,10))
    source=(e[-1]-e[0])+(x[-1]-x[0])+(y[-1]-y[0])+(z[-1]-z[0])+loss+load-control
    return e,x,y,z,loss,load,source,control

@pytest.mark.parametrize("seed",[668,369,1524,20261117,7,13,61,83])
def test_space_time_all_four_axes_exact_100_cases_per_seed(seed):
    for k in range(100):
        assert space_time_balance(*genuine_window(seed*1000+k))

def test_negative_signed_environmental_source_is_allowed():
    e=[Q(5),Q(2)]
    x=[Q(0),Q(0)]
    y=[Q(0),Q(0)]
    z=[Q(0),Q(0)]
    assert space_time_balance(e,x,y,z,Q(0),Q(0),Q(-3),Q(0))

def test_source_off_cannot_pretend_storage_discharge_is_replenishment():
    e=[Q(10),Q(4)]
    face=[Q(0),Q(0)]
    assert space_time_balance(e,face,face,face,Q(1),Q(5),Q(0),Q(0))
    assert e[-1]!=e[0] # Not a repeatable restored donor cycle

def test_controller_ionisation_cost_cannot_be_silently_omitted():
    e=[Q(4),Q(4)]; zero=[Q(0),Q(0)]
    assert space_time_balance(e,zero,zero,zero,Q(6),Q(4),Q(0),Q(10))
    assert not space_time_balance(e,zero,zero,zero,Q(6),Q(4),Q(0),Q(9))

def test_signed_external_face_orientation_matters():
    e=[Q(0),Q(0)]
    x=[Q(2),Q(7)]
    zero=[Q(0),Q(0)]
    assert space_time_balance(e,x,zero,zero,Q(0),Q(0),Q(5),Q(0))
    flipped=[-v for v in x]
    assert not space_time_balance(e,flipped,zero,zero,Q(0),Q(0),Q(5),Q(0))

def test_three_axis_open_boundary_not_periodic():
    e=[Q(2),Q(2)]
    x=[Q(1),Q(5)]
    y=[Q(3),Q(4)]
    z=[Q(-2),Q(0)]
    assert space_time_balance(e,x,y,z,Q(0),Q(0),Q(7),Q(0))
    assert sum((partial(v) for v in (x,y,z)),Q(0))==Q(7)

def test_face_sample_does_not_identify_real_original_solar_input():
    # A model's local algebra does not supply an independently observed
    # source. The test requires that source work be passed explicitly.
    e=[Q(0),Q(0)]
    zero=[Q(0),Q(0)]
    assert space_time_balance(e,zero,zero,zero,Q(0),Q(0),Q(0),Q(0))
    assert not space_time_balance(e,zero,zero,zero,Q(0),Q(3),Q(0),Q(0))

def test_natural_boundary_input_not_double_counted_as_volume_source():
    e=[Q(0),Q(0)]
    # Negative outward Poynting means 4 work units ENTER the exterior face.
    x=[Q(0),Q(-4)]
    z=[Q(0),Q(0)]
    # Correct: the 4-unit load is paid by the signed boundary, with no
    # extra fictitious natural volume current.
    assert space_time_balance(e,x,z,z,Q(0),Q(4),Q(0),Q(0))
    # Incorrect: claiming ANOTHER 4 units of independent solar volume
    # input double counts the same incoming 4 boundary units.
    assert not space_time_balance(e,x,z,z,Q(0),Q(4),Q(4),Q(0))

def test_explicit_material_controller_cost_split():
    e=[Q(0),Q(0)]
    x=[Q(0),Q(-5)]
    z=[Q(0),Q(0)]
    ohmic,ADE,chemical=Q(1,2),Q(1,3),Q(1,6)
    controller,modulator,ion_pump,neutral=Q(1,4),Q(1,2),Q(1),Q(-1,4)
    assert ohmic+ADE+chemical==Q(1)
    assert controller+modulator+ion_pump+neutral==Q(3,2)
    # Load of 5.5 is paid by natural face 5 plus volume pump 1.5
    # minus 1 of physical loss, not by nominal natural face alone.
    assert space_time_balance(
        e,x,z,z,ohmic+ADE+chemical,Q(11,2),Q(0),
        controller+modulator+ion_pump+neutral)
    assert not space_time_balance(
        e,x,z,z,ohmic+ADE+chemical,Q(11,2),Q(0),
        controller+modulator+neutral) # dropped ion pump
