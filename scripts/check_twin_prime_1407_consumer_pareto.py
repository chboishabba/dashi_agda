#!/usr/bin/env python3
"""PR #1407 -> #1408 consumer-specific information-loss cross-check.

Historical math: finite Fourier/convolution index aliasing (Orszag/Patterson).
Existing original PR #1407 owners: 27x729 incidence, 4^3 retained / 5^3 full.
Existing #1408 owners: certified CRT sieve and signed exponent arithmetic.
This is a finite exact-integer probe, NOT Agda kernel evidence or new prime math.
"""
from itertools import product
from math import isqrt, prod


def prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n)+1))


def twins(n):
    return prime(n) and prime(n+2)


def mod_point(point, size):
    return tuple(x % size for x in point)


def main():
    modes = list(product((-1,0,1), repeat=3))
    pairs = list(product(modes,repeat=2))
    assert len(modes) == 27 and len(pairs) == 729
    sum_point = lambda a,b: tuple(x+y for x,y in zip(a,b))
    retained = [sum_point(a,b) for a,b in pairs if all(-1 <= x+y <= 1 for x,y in zip(a,b))]
    assert len(retained)==343 and len(pairs)-len(retained)==386
    wrong3=wrong4=wrong5=0
    for a,b in pairs:
        result=sum_point(a,b)
        for target in modes:
            actual=(result==target)
            wrong3 += (mod_point(result,3)==mod_point(target,3)) != actual
            wrong4 += (mod_point(result,4)==mod_point(target,4)) != actual
        for target in product((-2,-1,0,1,2),repeat=3):
            actual=(result==target)
            wrong5 += (mod_point(result,5)==mod_point(target,5)) != actual
    assert wrong3 > 0 and wrong4 == 0 and wrong5 == 0
    assert mod_point((-2,0,0),4)==mod_point((2,0,0),4)
    assert (5 % 6)==(35 % 6)==5
    assert twins(5) and not twins(35)
    assert 8%2==0 and 3%2==1
    primes=(2,3,5,7,11)
    period=prod(primes)
    survivor=lambda n: all(n%p!=0 and (n+2)%p!=0 for p in primes)
    for n in range(1,2000):
        assert survivor(n)==survivor(n+period)
        for p in primes:
            count=sum(1 for r in range(p) if r%p and (r+2)%p)
            assert count == (1 if p==2 else p-2)
    # Survives all five prime-modulus tests, but not genuine primality.
    assert survivor(221) and not twins(221)  # 221 = 13*17
    print('27 inputs, 729 ordered pairs; exact retained=343, outside=386: PASS')
    print(f'3-grid retained mismatches={wrong3}; 4-grid retained mismatches={wrong4}; 5-grid full mismatches={wrong5}')
    print('same mod6 at 5/35 yet distinct twin truth; decoded p=3 differs from 2^3 parity: PASS')
    print(f'finite product-period={period} and prime-2 exception: PASS')
    print('No Agda kernel / no analytic prime-correlation claim')


if __name__=='__main__':
    main()
