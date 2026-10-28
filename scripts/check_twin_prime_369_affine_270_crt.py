#!/usr/bin/env python3
"""Independent exhaustive local audit of ternary-27 affine CRT 270 codec.

Original mathematics: finite CRT/Brun local sieve, C2 orbit theory.
Reuse exact DASHI geometry and separately owned Ibrahim 3x5 quotient.
Not Agda kernel, not Monster same-object, not twin-prime infinitude.
"""
from itertools import product

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
    for cube_point,value in encoding.items():
        assert decoding[value]==cube_point and survives(value)
        assert value%2==1 and value%3==2 and value%5 in (1,2,4)
        assert encoding[antipode(cube_point)]==(-value-2)%270
    assert encoding[(0,0,0)]==269
    assert len({min(p,antipode(p)) for p in cube})==14
    assert len({(p[0],min(p[1:],antipode(p)[1:])) for p in cube})==15
    assert 27==1+13*2 and 9==1+4*2
    assert 3**5==243 and 5**3==125 and 3**9==19683
    print('PASS: 27 exact survivors modulo 270 (p=2,3,5)')
    print('PASS: explicit affine cube↔finite survivor lookup and 27 C2 swaps')
    print('PASS: one fixed 269 + 13 antipodal pairs; separate 3x5=15 quotient')
    print('Theorem level: finite Python only; Agda code is kernel pending')

if __name__=='__main__':
    main()
