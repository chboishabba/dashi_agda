#!/usr/bin/env python3
"""Actual e^(i 99^k) versus torsion/C3 projections: cross-PR regression.

Uses the existing Pickover code *as owners*:
  check_pickover_fast_sine_complex_power.power_certified (Taylor e^i)
  check_pickover_machin_factorial_phase.interval_pi (Machin 1706)

The paired horned-C3 PR #1244 owns the actual 2I / SU2 quaternion
calculation q^3=-I. This independent script does not copy or import
that unmerged implementation and must not identify these observables.

Classical sources: Machin; de Moivre/Euler; Lindemann (1882),
Weierstrass (1885) for the PAPER theorem e^(iN) transcendental for N>0.
DASHI supplies source-specific finite arithmetic and negative controls.
"""
from math import factorial
from check_pickover_fast_sine_complex_power import power_certified
from check_pickover_machin_factorial_phase import interval_pi

def machin_sign_integer_angle(N, scale, L, U):
    """If floor(N/pi) is unambiguous, (-1)^floor is the exact sine sign."""
    lo=(N*scale)//U
    hi=(N*scale)//L
    assert lo==hi,(lo,hi)
    return 1 if lo%2==0 else -1

def powered_sign(N):
    for digits in (20,50,100,200,350,500):
        sign,ops,error=power_certified(N,digits)
        if sign is not None:
            assert error < 10**digits
            return sign,digits,ops
    raise AssertionError('precision schedule too short')

def run():
    # 325-digit Machin enclosure: adequate for these selected finite
    # exponents through 99^120; nowhere near the 9999! target.
    scale=10**325
    lower,upper=interval_pi(scale)
    assert 3*scale<lower<upper<4*scale
    values={}
    for k in (1,6,9,18,24,120):
        N=99**k
        sM=machin_sign_integer_angle(N,scale,lower,upper)
        sP,digits,ops=powered_sign(N)
        assert sM==sP,(k,sM,sP)
        assert N%3==0 and N%9==0 and N%11==0
        values[k]=(sM,digits,ops)
    # Same coarse C3 sector / source valuations, opposite real signs.
    assert values[1][0]==-1 and values[6][0]==1
    # Both vanish in lambda^9 Eisenstein quotient because 99^3=0;
    # nonetheless their exact real angles have opposite signs.
    assert values[9][0]==-1 and values[18][0]==1

    E=factorial(9999)
    crt=pow(99,E,9999)
    assert crt==4950 and (crt*crt)%9999==crt
    assert tuple(crt%m for m in (9,11,101))==(0,0,1)
    assert pow(99,E,3)==0
    assert pow(99,E,1111)==506
    # The residue determines a projector on mu_9999 but does
    # NOT evaluate the actual phase exp(i 99^E).
    print('PASS independent Machin-vs-Taylor-complex-power real signs:')
    for k,(sgn,digits,ops) in values.items():
        print(f'  99^{k}: sign {sgn:+d}, fixed_precision={digits}, multiplies={ops}')
    print('PASS same C3/SSP orientation but opposite real sine signs')
    print('PASS same Eisenstein lambda^9 zero but opposite real signs')
    print('PASS 9999! CRT mu_9999 projector 4950 idempotent; mu3 image identity')
    print('PAPER-LEVEL: e^(iN) is not a root of unity for positive integer N')
    print('BOUNDARY: no sign certificate for sin(99^(9999!)); no wild SU2 holonomy')

if __name__=='__main__':
    run()
