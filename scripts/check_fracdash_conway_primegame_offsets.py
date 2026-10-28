#!/usr/bin/env python3
"""Conway's FAST PRIMEGAME, independently replayed against FRACDASH semantics.

Source: John H. Conway, FRACTRAN (1987), and fast variant in
OEIS A007546 / A203907 (not the 1/7 variant, which requires a DIFFERENT
ordered fraction set). The FRACDASH R3 signed-register macro comes from
chboishabba/FRACDASH BRIDGE_CORRECTNESS.md, physics1 gold slice.

Source arithmetic is first-applicable integer FRACTRAN.
Do not equate register-tag primes with generated arithmetic primes;
+/-2 is only an independently computed integer readout here.
"""
from math import isqrt

FAST_PRIMEGAME = ((17,91),(78,85),(19,51),(23,38),(29,33),
                  (77,29),(95,23),(77,19),(1,17),(11,13),
                  (13,11),(15,14),(15,2),(55,1))

def is_prime(n):
    return n >= 2 and all(n % k for k in range(2,isqrt(n)+1))

def first_step(state, rules):
    for i, (numerator, denominator) in enumerate(rules):
        if state % denominator == 0:
            return state // denominator * numerator, i
    return None

def output_exponents(steps=20000):
    state = 2
    for tick in range(steps + 1):
        if state > 2 and state & (state-1) == 0:
            exponent = state.bit_length()-1
            yield tick, exponent
        move = first_step(state, FAST_PRIMEGAME)
        if move is None:
            return
        state, index = move

def check():
    outputs=list(output_exponents())
    assert [p for step,p in outputs[:9]] == [2,3,5,7,11,13,17,19,23]
    assert [t for t,p in outputs[:9]] == [19,69,280,707,2363,3876,8068,11319,19201]
    assert all(is_prime(p) for _,p in outputs)
    # FRACDASH signed physics1: R3 negative -> zero -> positive
    reg=23
    for fraction in ((17,23),(19,17)):
        numerator,denominator=fraction
        assert reg % denominator == 0
        reg = reg // denominator * numerator
    assert reg == 19
    # Exponent readout p +/-2 is independent arithmetic, not a PRIMEGAME
    # output state and not automatically prime.
    twins=[(p,p+2) for _,p in outputs if is_prime(p+2)]
    assert (3,5) in twins and (5,7) in twins and (11,13) in twins
    assert not is_prime(13+2)
    print('FAST PRIMEGAME emissions (step,p,p-2 prime?,p+2 prime?):')
    for t,p in outputs[:9]:
        print(t,p,is_prime(p-2),is_prime(p+2))
    print('R3 register 23 -> 17 -> 19: PASS')
    print('Distinct: prime-game 2^p outputs, signed prime-tag registers, +/-2 arithmetic')
    print('Finite execution only; historical general enumeration theorem is Conway-owned')
if __name__ == '__main__':
    check()
