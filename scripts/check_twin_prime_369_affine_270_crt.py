#!/usr/bin/env python3
"""Independent exhaustive local audit of ternary-27 affine CRT 270 codec.

Original mathematics: finite CRT/Brun local sieve, C2 orbit theory.
Reuse exact DASHI geometry and separately owned Ibrahim 3x5 quotient.
Not Agda kernel, not Monster same-object, not twin-prime infinitude.
"""
from itertools import product
from math import isqrt

def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))

def true_twin_start(n):
    return is_prime(n) and is_prime(n + 2)

TRITS=(-1,0,1)
digit=lambda t:t+1
affine270=lambda p:(41+108*digit(p[0])+30*digit(p[1])+90*digit(p[2]))%270
antipode=lambda p:tuple(-x for x in p)
cube=list(product(TRITS, repeat=3))
encoding={p:affine270(p) for p in cube}
decoding={value:point for point,value in encoding.items()}
survives=lambda n:all(n%p!=0 and (n+2)%p!=0 for p in (2,3,5))

def main():
    assert len(cube)==3*3*3==len(encoding)==len(decoding)==27
    arithmetic_survivors={n for n in range(270) if survives(n)}
    assert set(decoding)==arithmetic_survivors
    # All 270 coverage cases match exactly: 27 accepted, 243 rejected.
    rejected={n for n in range(270) if not survives(n)}
    assert len(rejected)==243
    assert all(any((n+offset)%q==0 for q in (2,3,5) for offset in (0,2)) for n in rejected)
    for cube_point,value in encoding.items():
        assert decoding[value]==cube_point and survives(value)
        assert value%2==1 and value%3==2 and value%5 in (1,2,4)
        x,y,z=(digit(t) for t in cube_point)
        assert value%27==(14+3*y+9*z)%27
        assert value%5==(1+3*x)%5
        assert encoding[antipode(cube_point)]==(-value-2)%270
    # A FULL typed-cube survivor with both endpoints actually composite.
    assert encoding[(0,1,1)]==119
    assert 119==7*17 and 121==11*11
    assert survives(119)
    # Genuine consumer collision INSIDE the sieve's full 27-state image.
    first, second = encoding[(0,-1,1)], encoding[(0,1,-1)]
    assert (first,second)==(59,209)
    assert survives(first) and survives(second)
    assert true_twin_start(first) and not true_twin_start(second)
    assert second==11*19
    # Original Ibrahim's 3x5 reduction retains x, identifies inner antipodes.
    assert (0,1,-1)==(0,-(-1),-(1))
    assert encoding[(0,0,0)]==269
    assert len({min(p,antipode(p)) for p in cube})==14
    assert len({(p[0],min(p[1:],antipode(p)[1:])) for p in cube})==15
    assert 27==1+13*2 and 9==1+4*2
    assert 3**5==243 and 5**3==125 and 3**9==19683
    print('PASS: 270 exhaustive proof-table cases, 27 survivors, 243 rejected')
    print('PASS: exact 1 x 9 x 3 residue projections: mod 2, mod 27, mod 5')
    print('PASS: code 119 => 119 = 7*17 and 121 = 11*11 (both composite)')
    print('PASS: explicit affine cube↔finite survivor lookup and 27 C2 swaps')
    print('PASS: 59/209 same inner-phase orbit within wheel; true twin vs composite')
    print('PASS: one fixed 269 + 13 antipodal pairs; separate 3x5=15 quotient')
    print('Theorem level: finite Python only; Agda code is kernel pending')

if __name__=='__main__':
    main()
