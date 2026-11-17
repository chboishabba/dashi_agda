#!/usr/bin/env python3
"""Exact full-vector Poynting sample / face-normal reversal checks.

Uses rational vector values. This is a finite surface-sample algebra test,
not a space-time integrated Maxwell or atmospheric-source calculation.
"""
from fractions import Fraction
from random import Random
import pytest
from test_smith_filsinger_indexed_face_incidence_exact import (
    Face, signed_face_pair_total
)

def dot(a,b):return sum((x*y for x,y in zip(a,b)),Fraction(0))

def cross(a,b):
    return (a[1]*b[2]-a[2]*b[1],
            a[2]*b[0]-a[0]*b[2],
            a[0]*b[1]-a[1]*b[0])

def sampled_face_flux(e,b,n,weight=Fraction(1)):
    return weight*dot(n,cross(e,b))

def neg(a):return tuple(-x for x in a)

@pytest.mark.parametrize("seed",[668,369,1524,20261117])
def test_3d_full_vector_normal_reversal(seed):
    rng=Random(seed)
    for k in range(250):
        E=tuple(Fraction(rng.randrange(-11,12),rng.randrange(1,9))
                for _ in range(3))
        B=tuple(Fraction(rng.randrange(-11,12),rng.randrange(1,9))
                for _ in range(3))
        n=tuple(Fraction(rng.randrange(-11,12),rng.randrange(1,9))
                for _ in range(3))
        weight=Fraction(rng.randrange(1,10),rng.randrange(1,9))
        src=sampled_face_flux(E,B,n,weight)
        dst=sampled_face_flux(E,B,neg(n),weight)
        assert src+dst==0
        assert src==-dst

def test_actual_field_cross_not_arbitrary_phasor():
    E=(Fraction(1),Fraction(0),Fraction(0))
    B=(Fraction(0),Fraction(1),Fraction(0))
    n=(Fraction(0),Fraction(0),Fraction(1))
    assert cross(E,B)==n
    assert sampled_face_flux(E,B,n,Fraction(3,2))==Fraction(3,2)
    assert sampled_face_flux(E,B,neg(n),Fraction(3,2))==Fraction(-3,2)

def test_wrongly_oriented_face_fails_signed_cancellation():
    E=(Fraction(1),Fraction(0),Fraction(0))
    B=(Fraction(0),Fraction(1),Fraction(0))
    n=(Fraction(0),Fraction(0),Fraction(1))
    left=sampled_face_flux(E,B,n)
    wrong_right=sampled_face_flux(E,B,n)
    assert left+wrong_right != 0

def test_branched_signed_flux_with_nonzero_rational_values():
    faces=[Face(10,0,1,3),Face(11,0,2,4),Face(12,2,3,0)]
    signed=[Fraction(-7,3),Fraction(19,11),Fraction(0)]
    assert signed_face_pair_total(faces,signed)==0

def test_mismatched_source_target_flux_is_detectable():
    signed_src=Fraction(3,7)
    signed_dst=Fraction(-2,7)
    assert signed_src+signed_dst != 0

def test_loop_is_not_valid_internal_face():
    a=Face(7,1,1,10)
    assert a.source==a.target
