#!/usr/bin/env python3
"""A1 finite-support ALL-MODE rational Elsasser witness; no measured MMS claim.

Original exact selectedPlusTransfer law:
 Re[-i (zMinus(p)·q) <zPlus(k),zPlus(q)>_Hermitian]
with p=(1,0,0), q=(0,1,0), k=p+q.
Coefficients at negative modes are conjugates; every other mode is zero.
The exact all-mode Agda IdealElsasserFourierState remains an OPEN weld.
"""
from fractions import Fraction as Q
from itertools import product
import json

p=(1,0,0);q=(0,1,0);k=(1,1,0)
def neg(m):return tuple(-a for a in m)
def plus(m):
    return {q:(1+0j,0j,0j),neg(q):(1+0j,0j,0j),
            k:(1+0j,-1+0j,0j),neg(k):(1+0j,-1+0j,0j)
           }.get(m,(0j,0j,0j))
def minus(m,sgn):
    return {p:(0j,sgn*1j,0j),neg(p):(0j,-sgn*1j,0j)
           }.get(m,(0j,0j,0j))
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def hermitian(a,b):return sum(x.conjugate()*y for x,y in zip(a,b))
def squared(v):return sum((z.conjugate()*z).real for z in v)
def magnetic(m,sgn):
    return tuple((a-b)/2 for a,b in zip(plus(m),minus(m,sgn)))
def transfer(sgn):
    return (-1j*dot(minus(p,sgn),tuple(complex(a) for a in q))
            *hermitian(plus(k),plus(q))).real

def check():
    n=0
    for sign in (1,-1):
        for mode in product(range(-3,4),repeat=3):
            assert plus(neg(mode))==tuple(z.conjugate() for z in plus(mode))
            assert minus(neg(mode),sign)==tuple(z.conjugate()
                    for z in minus(mode,sign))
            assert dot(plus(mode),mode)==0
            assert dot(minus(mode,sign),mode)==0
            n+=1
        assert transfer(sign)==sign
        assert squared(magnetic(k,sign))==Q(1,2)
        assert squared(magnetic(q,sign))==Q(1,4)
    assert transfer(1)+transfer(-1)==0
    # Same pointwise z+/z- values at x=(0,0,0) for opposite
    # modal-transfer signs. The imaginary +/- p conjugate pair cancels
    # at the origin, but its first x derivative changes sign.
    def local_origin(sign):
        supported=(p,neg(p),q,neg(q),k,neg(k))
        zplus=tuple(sum(plus(m)[j] for m in supported) for j in range(3))
        zminus=tuple(sum(minus(m,sign)[j] for m in supported) for j in range(3))
        return zplus,zminus
    assert local_origin(1)==local_origin(-1)==(
        (4+0j,-2+0j,0j),(0j,0j,0j))
    # d_x zMinus at x=0 is i*sum_m m_x zMinus(m).
    def minus_x_gradient_at_origin(sign):
        return tuple(1j*sum(m[0]*minus(m,sign)[j]
                            for m in (p,neg(p))) for j in range(3))
    assert minus_x_gradient_at_origin(1)==(0j,-2+0j,0j)
    assert minus_x_gradient_at_origin(-1)==(0j,2+0j,0j)

    return {
       "status":"PASS","source":"DASHI/Physics/Plasma/KSW668MHDSelectedStateTransferExact.agda",
       "original_p_q_k":[p,q,k],
       "positive_zplus_q":[1,0,0],
       "positive_zplus_k":[1,-1,0],
       "positive_zminus_p_signs":["+i e_y","-i e_y"],
       "global_definition":"conjugate at negative modes; zero at all other integer Fourier modes",
       "signed_lattice_mode_checks":n,
       "physical_B_strength_k":"1/2","physical_B_strength_q":"1/4",
       "positive_transfer":"+1","negative_transfer":"-1",
       "all_mode_Agda_state_constructed":False,
       "instrument_calibrated_same_event_MMS":False,
       "both_states_local_origin_zplus":"(4,-2,0)",
       "both_states_local_origin_zminus":"(0,0,0)",
       "sign_plus_minus_first_x_derivative":"(0,-2,0) vs (0,+2,0)",
       "exact_single_point_identifiability_no_go":"same z+/z- local field, opposite Fourier transfer"
    }
if __name__=="__main__":
    print(json.dumps(check(),indent=2))
