#!/usr/bin/env python3
"""Source-bounded 27D bosonic-M dilaton mismatch repair test.

Original prior physics: Horowitz/Susskind; Lambert/West; Glennon/West.
This file is a conditional off-shell coefficient calculation, not a K27
representation, generally covariant 27D alternative theory, or BRST proof.
"""
from fractions import Fraction as F
from itertools import product


def coefficients(d, a):
    a = F(a)
    b = -2*a  # demanded by common R and C_{..y} string-frame weight
    exponent_R = (d-2)*a + b
    exponent_H = (d-6)*a - b
    assert exponent_R == exponent_H == (d-4)*a
    gravity = (d-1)*(d-6)*a*a
    string = (d-4)**2*a*a
    gap = gravity-string
    assert gap == (d-10)*a*a
    return b, exponent_R, gravity, string, gap


def repair(d, a):
    b, p, g, target, gap = coefficients(d,a)
    # A supplementary 27D scalar chi with canonical -1/2 |d chi|^2,
    # formally restricted via chi=k sigma, changes K by -k^2/2.
    # We solve for k^2 exactly, without choosing sqrt(k^2).
    k2 = 2*gap
    assert g-k2/F(2) == target
    # Standard real positive-norm scalar requires k2>=0.
    assert (k2 >= 0) == (d>=10 or gap==0)
    return b, p, k2


def test():
    tested=0
    for d, numer, denom in product(range(7,41),(-7,-2,1,3,8),(1,2,5)):
        a=F(numer,denom)
        b,p,k2=repair(d,a)
        tested+=1
        assert k2 == 2*(d-10)*a*a
    assert tested == 510
    print('PASS', tested, 'exact string-frame coefficients and formal extra-scalar repairs')
    b,p,k2=repair(26,F(1))
    assert (b,p,k2) == (-2,22,32)
    assert F(500)-F(32,2)==484
    print('PASS d=26 canonical scalar requires (dchi/dsigma)^2=32 a^2, formally 500-16=484')
    assert repair(10,F(1))[2] == 0
    assert repair(9,F(1))[2] == -2
    print('PASS d=10 needs no scalar repair; d<10 would demand negative squared slope in this ansatz')

    # Any chi=k*sigma is an imposed single-field constraint, NOT a consequence
    # of a 27D free scalar EOM. For sigma=t on flat 26D Minkowski base,
    # Box_g sigma=0, |d sigma|^2_g=-1. The full lifted wave operator is
    # Box_G chi=k exp(-2 a sigma) * [Box_g sigma + p |d sigma|²].
    # The bracket at d=26, a=1 is therefore -22, NONZERO.
    b,p,k2=repair(26,F(1))
    assert -p == -22
    assert k2 != 0
    print('NO-GO free 27D spectator chi=k*sigma: flat-base sigma=t gives Box_G chi=-22*k*exp(-2*t) != 0')
    print('BOUNDARY does not exclude an independently specified new 27D interacting scalar action')

    # Alternative natural 3-form reduction: B = C_y, so F_y=dB, with no
    # dr ^ B, even if radial scalar varies. In contrast the
    # field redefinition C_y=r B introduces dr ^ B.
    B12=F(2); r=F(3); dr_dt=F(1); H012=F(0)
    without_rescale=H012
    with_rescale=r*H012 + dr_dt*B12
    assert without_rescale==0 and with_rescale==2
    print('PASS corrected source scope: dr^B arises only in radion-rescaled B chart, not B=C_y')
    print('STOP: no off-shell consistent scalar truncation, K27 preservation, or quantum string shown')


if __name__ == '__main__':
    test()
