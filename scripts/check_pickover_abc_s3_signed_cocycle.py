#!/usr/bin/env python3
"""Exact S3 ABC position cocycle / C3 phase correction / signed-zero cut.

Prior art: DASHI TernaryPermutationS3LawsExact,
TernaryHypervoxelPermutationTransportExact,
TrialecticGrothendieckTransitionCocycleExact,
TorqueTrialectic369Exact (merged PR 1164),
NSTriadKNTriadS3RealityActionRound35Exact,
SignedZeroTernaryOrientationExact, oriented-zero wave models.
DASHI Pickover specialization: weighted address difference under 99.
This is NOT a sine(99^(9999!)) certificate.
"""
from collections import Counter
from fractions import Fraction
from itertools import permutations, product

PERMS = tuple(permutations(range(3)))
DIGITS = tuple(product(range(3), repeat=3))

def act(sigma, abc):
    return tuple(abc[i] for i in sigma)

def compose(sigma, tau):
    """Act by tau, then sigma."""
    return tuple(tau[i] for i in sigma)

def parity(sigma):
    crossings = sum(sigma[i] > sigma[j]
                    for i in range(3) for j in range(i + 1, 3))
    return -1 if crossings % 2 else +1

def torque(abc):
    return 0 if len(set(abc)) < 3 else parity(abc)

def value(abc):
    return 9 * abc[0] + 3 * abc[1] + abc[2]

def phase(abc, tail):
    assert 0 < tail < 1
    return (value(abc) + tail) / 27

def complement(abc):
    return tuple(2 - i for i in abc)

def circle(x):
    return x % 1

def sine_sign(x):
    x = circle(x)
    return 0 if x in (0, Fraction(1, 2)) else (1 if x < Fraction(1, 2) else -1)

def delta(sigma, abc):
    return value(act(sigma, abc)) - value(abc)

def correction(sigma, abc):
    """The correction to the 99-power phase lives in C3."""
    return circle(Fraction(11 * delta(sigma, abc), 3))

def check_s3():
    assert Counter(map(parity, PERMS)) == {1: 3, -1: 3}
    for sigma, tau in product(PERMS, repeat=2):
        joined = compose(sigma, tau)
        assert joined in PERMS
        assert parity(joined) == parity(sigma) * parity(tau)
        for abc in DIGITS:
            assert act(sigma, act(tau, abc)) == act(joined, abc)
            assert delta(joined, abc) == delta(tau, abc) + delta(sigma, act(tau, abc))
            assert correction(joined, abc) == circle(
                correction(tau, abc) + correction(sigma, act(tau, abc)))
            assert torque(act(sigma, abc)) == parity(sigma) * torque(abc)
    assert Counter(map(torque, DIGITS)) == {0: 21, 1: 3, -1: 3}
    # Six genuine S3 actions give all six (parity, rational C3 carry)
    # labels on any all-distinct ABC word. Retain the rational phase
    # correction modulo 1; integer floor destroys the C3 remainder.
    for abc in DIGITS:
        if len(set(abc)) < 3: continue
        pairs={(parity(p), correction(p, abc)) for p in PERMS}
        assert pairs == {(sign, Fraction(k, 3)) for sign in (-1,1) for k in range(3)}
    print("PASS six parity × rational-C3 carry labels on nondegenerate ABC words")
    print("PASS S3 ABC composition / additive phase cocycle / torque sign")

def check_99_and_reflection():
    tails = (Fraction(1,11), Fraction(1,4), Fraction(1,2), Fraction(7,9))
    for abc, sigma, tail in product(DIGITS, PERMS, tails):
        x = phase(abc, tail)
        y = phase(act(sigma,abc), tail)
        assert y - x == Fraction(delta(sigma, abc), 27)
        assert circle(99*y) == circle(99*x + correction(sigma,abc))
        assert circle(99*x) == circle(Fraction(11 * (abc[2] + tail), 3))
        assert correction(sigma, abc) in (Fraction(0),Fraction(1,3),Fraction(2,3))
        reflected = phase(complement(abc), 1-tail)
        assert reflected == 1-x
        assert circle(99*reflected) == circle(-99*x)
        assert sine_sign(reflected) == -sine_sign(x)
    a,b=(0,1,2),(1,2,0)
    assert torque(a) == torque(b) == 1
    assert sine_sign(phase(a,Fraction(1,2))) == 1
    assert sine_sign(phase(b,Fraction(1,2))) == -1
    print("PASS real phase x->99x C3 correction; complement anti-phase")
    print("COUNTEREXAMPLE even S3 parity does not decide real sine sign:",a,b)

def orbit_sizes(flip):
    unseen = set(DIGITS); sizes=[]
    while unseen:
        abc=next(iter(unseen))
        states={act(p,complement(abc) if bit else abc)
                for p,bit in product(PERMS, (0,1) if flip else (0,))}
        sizes.append(len(states))
        unseen.difference_update(states)
    return Counter(sizes)

def check_orbits():
    assert orbit_sizes(False)=={1:3,3:6,6:1}
    assert orbit_sizes(True)=={6:4,2:1,1:1}
    print("PASS 27 S3 orbits 3x1 + 6x3 + 1x6")
    print("PASS 27 S3 x C2 orbits 1x1 + 1x2 + 4x6; actions != orbit sizes")


def trit_multiply_11(digits_least_first):
    """Finite carry machine in Z3, NOT a Euclidean fractional-digit oracle."""
    carry = 0
    output = []
    for digit in digits_least_first:
        z = 11 * digit + carry
        output.append(z % 3)
        carry = z // 3
        assert 0 <= carry <= 10
    return output, carry

def check_carry_transducer():
    for depth in range(1, 8):
        modulus = 3 ** depth
        for n in range(modulus):
            inp = tuple((n // 3 ** j) % 3 for j in range(depth))
            out, carry = trit_multiply_11(inp)
            lower = sum(d * 3 ** j for j, d in enumerate(out))
            assert 11 * n == lower + carry * modulus
            assert lower == (11 * n) % modulus
            assert carry == (11 * n) // modulus
    # C2 reflection conjugates C3 carry phase under address complement:
    for abc, permutation in product(DIGITS, PERMS):
        assert correction(permutation, complement(abc)) == circle(-correction(permutation, abc))
    print("PASS p=3 carry transducer for x11, depths 1..7, <=11 carry states")
    print("PASS C2 complement reverses address-dependent C3 cocycle")

if __name__ == "__main__":
    check_s3()
    check_99_and_reflection()
    check_orbits()
    check_carry_transducer()
    print("OPEN source-specific alpha=1/(2*pi) first noncentral digit at 9999!")
