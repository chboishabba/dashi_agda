#!/usr/bin/env python3
"""Independent exact finite x/y/z numerology cross-pollination.

Reuse and distinguish existing theorem owners:
  Geometry.Ternary27Point, AntipodalOrbitExact, Ibrahim phase-preserving
  3x5=15 quotient, Base369 NDimParetoChartExact (nine axes).
  Arithmetic prime-3 local sieve is an independent certified-prime
  consumer. Conway/Guy 14-rule FRACTRAN programme is a DIFFERENT 14.
This script is finite regression; no Agda kernel or Monster same-object.
"""
from itertools import product
T = (-1, 0, 1)
pts = list(product(T, repeat=3))
neg = lambda p: tuple(-x for x in p)
global_class = lambda p: min(p,neg(p))
phase_class = lambda p: (p[0],min(p[1:],neg(p[1:])))
centered = lambda y,z: (-1 + 3*y + 9*z) % 27
sieve = lambda n,primes: all(n%p and (n+2)%p for p in primes)

def main():
    assert len(pts) == 3*3*3 == 27
    assert len({global_class(p) for p in pts}) == 14
    assert len({phase_class(p) for p in pts}) == 3*5 == 15
    assert len(list(product(pts, repeat=2))) == 729
    assert 27 == 1+13*2 and 9 == 1+4*2
    plane = tuple(product(T, repeat=2))
    reps = {centered(y,z) for y,z in plane}
    assert len(reps) == 9
    assert reps == {n for n in range(27) if sieve(n,(3,))}
    for y,z in plane:
        n = centered(y,z)
        rev = centered(-y,-z)
        assert rev == (-n-2)%27
        assert n % 3 == 2 and (n+2)%3 == 1
        assert phase_class((0,y,z))==phase_class((0,-y,-z))
    assert len({phase_class((0,y,z)) for y,z in plane}) == 5
    # 27 survivors mod 270 is a residue COUNT, not a canonical
    # isomorphism to the 27 trit cube.
    assert len([n for n in range(270) if sieve(n,(2,3,5))]) == 27
    assert 3**5 == 243 and 5**3 == 125 and 3**5 != 5**3
    assert 3**9 == 27**3 == 19683
    print('PASS: typed 3x3x3 cube -> 14 global classes and 3x5=15 inner-phase classes')
    print('PASS: prime-3 slice has 9 residues, affine swap -> 5 inner antipodal orbits')
    print('PASS: 27 finite CRT local survivors modulo 270; no same-object promotion')
    print('PASS: 3^5=243 != 5^3=125 and 3^9=19683')

if __name__ == '__main__':
    main()
