#!/usr/bin/env python3
"""Conway's PRIMEGAME, 14-fraction Richard K. Guy ordered variant.

Source: John H. Conway, FRACTRAN (1987), and Richard K. Guy (1983),
Conway's Prime Producing Machine (Math. Magazine 56(1), 26-33).
This is the 14-fraction 15/14,15/2 Guy variant, not Conway's 1/7
14-fraction presentation; compare OEIS A007546 and A267572. The FRACDASH R3 signed-register macro comes from
chboishabba/FRACDASH BRIDGE_CORRECTNESS.md, physics1 gold slice.

Source arithmetic is first-applicable integer FRACTRAN.
Do not equate register-tag primes with generated arithmetic primes;
+/-2 is only an independently computed integer readout here.
"""
from math import isqrt

CONWAY_GUY_FOURTEEN = ((17,91),(78,85),(19,51),(23,38),(29,33),
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
        move = first_step(state, CONWAY_GUY_FOURTEEN)
        if move is None:
            return
        state, index = move

def run_to_halt(state, rules):
    steps=0
    while True:
        move=first_step(state,rules)
        if move is None: return state,steps
        state,index=move
        steps+=1

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
    # A genuine two-step FRACTRAN computation of BOTH exponent offsets.
    # Input: 2^p * 3^2.  The 3-register is a two-unit step counter.
    # Ordered singleton programs [2/3] and [1/6] halt after exactly two
    # steps, producing 2^(p+2) and 2^(p-2) respectively (p>=2).
    for _,p in outputs:
        encoded=(2**p)*(3**2)
        plus,two_steps_plus=run_to_halt(encoded,((2,3),))
        minus,two_steps_minus=run_to_halt(encoded,((1,6),))
        assert two_steps_plus == two_steps_minus == 2
        assert plus == 2**(p+2), (p,plus)
        assert minus == 2**(p-2), (p,minus)
    # FRACTRAN computes the exact offsets, but makes no primality
    # assertion about them.
    twins=[(p,p+2) for _,p in outputs if is_prime(p+2)]
    assert (3,5) in twins and (5,7) in twins and (11,13) in twins
    assert not is_prime(13+2)
    print('Conway/Guy PRIMEGAME emissions (step,p,p-2 prime?,p+2 prime?):')
    for t,p in outputs[:9]:
        print(t,p,is_prime(p-2),is_prime(p+2))
    print('R3 register 23 -> 17 -> 19: PASS')
    print('FRACTRAN exponent offsets: 2^p*3^2 -> 2^(p+2) via [2/3],')
    print('                           2^p*3^2 -> 2^(p-2) via [1/6]: PASS')
    print('Distinct: prime-game 2^p outputs, signed prime-tag registers, genuine +/-2 FRACTRAN computations')
    print('Finite execution only; historical general enumeration theorem is Conway-owned')
if __name__ == '__main__':
    check()
