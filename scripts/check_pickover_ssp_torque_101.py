#!/usr/bin/env python3
"""Exact finite bridge: 99 FRACTRAN valuations, CRT mu9999 projector,
signed torsion-orientation. No floating point, no real sine or RH theorem.

Source owners: John Conway (FRACTRAN); classical CRT/circle geometry;
DASHI signed SSP, C3 spectral orientation and torque bracket consumers.
"""
from math import factorial
from collections import Counter

SSP_PRIMES = (2,3,5,7,11,13,17,19,23,29,31,41,47,59,71)

def valuation_99_power(k):
    assert k >= 0
    return {p: (2*k if p==3 else k if p==11 else 0) for p in SSP_PRIMES}

def signed_trit(v):
    return (v>0)-(v<0)

def oriented_area_sign_101(k):
    # Orientation of the 101st root exp(2*pi*i*k/101) using cyclic order.
    k %= 101
    return 0 if k==0 else (1 if k<=50 else -1)

def signed_3way_torque(orientation):
    # Exact finite right-hand-rule orientation, not a measured torque.
    assert orientation in (-1,0,1)
    return orientation

def transition_forward(k):
    # FRACTRAN fraction 99/1, restricted to input powers of 99.
    return k + 1

def transition_backward(k):
    # Reciprocal fraction 1/99 enabled precisely when k >= 1.
    return k-1 if k>=1 else None

def run():
    assert 99 == 3**2*11 and 9999 == 9*11*101
    assert 1111 == 11*101 and 10**4-1 == 9999
    e = factorial(9999)
    a = pow(99,e,9999)
    assert a == 4950 and pow(99,e,1111) == 506
    assert a*a%9999 == a and a == 99*50
    assert 50*99%101 == 1
    assert pow(99,factorial(10000),9999) == a

    for k in range(1,80):
        v = valuation_99_power(k)
        assert v[3]==2*k and v[11]==k
        assert v.keys()==set(SSP_PRIMES)
        assert sum(1 for p in v if v[p]>0)==2
        assert signed_trit(v[3])==signed_trit(v[11])==1
        assert valuation_99_power(transition_forward(k))[3]==v[3]+2
        assert valuation_99_power(transition_forward(k))[11]==v[11]+1
        assert transition_backward(transition_forward(k))==k
        assert transition_forward(transition_backward(k))==k
        for orientation in (-1,0,1):
            assert signed_3way_torque(-orientation)==-signed_3way_torque(orientation)

    observed = Counter()
    outputs = set()
    for k in range(9999):
        rk = (a*k)%9999
        outputs.add(rk)
        assert rk%99==0
        # zeta_9999^(99*t)=zeta_101^t with t=50*k mod101.
        t = 50*k%101
        assert rk==99*t
        s = oriented_area_sign_101(t)
        observed[s]+=1
        reflected = (a*(-k))%9999
        assert oriented_area_sign_101(reflected//99)==-s
        assert a*rk%9999==rk
    assert len(outputs)==101
    assert observed==Counter({-1:4950,0:99,1:4950}),observed

    # Machin's exact pi enclosures (separate script) give signs:
    # sin(99^1)<0 and sin(99^6)>0; both have the same coarse SSP sign.
    assert {p:signed_trit(v) for p,v in valuation_99_power(1).items()} == {
        p:signed_trit(v) for p,v in valuation_99_power(6).items()}

    print('PASS signed FRACTRAN 99/1: v3=2k, v11=k, other SSP lanes zero')
    print('PASS forward/backward symbolic exponent orbit; torque orientation reversal')
    print('PASS mu9999->mu101: 101 images, 99-fold fibres, sign distribution',dict(observed))
    print('PASS inversion, projector idempotence and 9999!/10000! finite projections')
    print('BOUNDARY: torsion signs and signed SSP polarity do not determine sin(99^(9999!))')

if __name__=='__main__':
    run()
