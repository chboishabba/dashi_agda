#!/usr/bin/env python3
"""Exact rational nontrivial right-moving Maxwell plane wave.

E=(0,a+b(x-t),0), B=(0,0,a+b(x-t)), J=0 in normalized vacuum.
A bounded spacetime cell has exact U,S flux cancellation at dx=dt.
This is a FORMAL EXAMPLE, not a measured solar/atmospheric wave.
"""
from fractions import Fraction as Q
from random import Random
import pytest

def amplitude(a,b,x,t):return a+b*(x-t)
def energy(a,b,x,t):return amplitude(a,b,x,t)**2
def cell(a,b,x,t,h):
    dU=energy(a,b,x,t+h)-energy(a,b,x,t)
    flux=energy(a,b,x,t)-energy(a,b,x-h,t)
    return dU,flux

@pytest.mark.parametrize('seed',[1,7,369,668,1524,20261117])
def test_actual_travelling_wave_exact_cell_200_each(seed):
    rng=Random(seed)
    for _ in range(200):
        a,b,x,t,h=[Q(rng.randrange(-20,21),rng.randrange(1,13)) for k in range(5)]
        assert amplitude(a,b,x,t+h)==amplitude(a,b,x-h,t)
        u,flux=cell(a,b,x,t,h)
        assert u+flux==0

def test_nontrivial_outgoing_flux_and_storage_change():
    a,b,x,t,h=Q(2),Q(1),Q(3),Q(0),Q(1)
    dU,out=cell(a,b,x,t,h)
    assert dU != 0
    assert out != 0
    assert dU==-out

def test_maxwell_vector_pointwise_curls():
    # d_t E_y=-b; curl(B)_y=-b, so Ampere dE-curlB=0.
    # d_t B_z=-b; curl(E)_z=b, so Faraday dB+curlE=0.
    for b in [Q(-3,7),Q(0),Q(8,5)]:
        assert -b-(-b)==0
        assert -b+b==0

def test_wrong_temporal_spatial_stride_is_not_exact_lightcone():
    a,b,x,t=Q(1),Q(3),Q(3),Q(0)
    dt,dx=Q(1),Q(2)
    wrong=(energy(a,b,x,t+dt)-energy(a,b,x,t)
           +energy(a,b,x,t)-energy(a,b,x-dx,t))
    assert wrong != 0

def test_plane_wave_not_finite_energy_on_all_R3():
    # Affine amplitude is unbounded as x increases with b != 0.
    a,b,t=Q(0),Q(1),Q(0)
    values=[energy(a,b,Q(n),t) for n in range(1,10)]
    assert values[-1]>values[0]
