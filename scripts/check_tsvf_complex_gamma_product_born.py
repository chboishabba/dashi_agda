#!/usr/bin/env python3
"""Reference check of original DASHI rational-complex gamma-product Born laws.

Finite complex amplitudes gamma_j=(a+bi) with exact Fraction coordinates.
Tests norm(product gamma)=product(norm gamma), conjugation and phase i invariance.
Does NOT populate physical TSVF 2017 disturbance/environment states, OS clock,
complex Hilbert completion, real measurement, or Agda kernel.
"""
from fractions import Fraction as F
from random import Random

def mul(x: tuple[F,F], y: tuple[F,F]) -> tuple[F,F]:
    a,b=x; c,d=y
    return a*c-b*d,a*d+b*c

def conj(x: tuple[F,F]) -> tuple[F,F]:
    return (x[0],-x[1])

def norm(x: tuple[F,F]) -> F:
    return x[0]*x[0]+x[1]*x[1]

def prod(xs: list[tuple[F,F]]) -> tuple[F,F]:
    result=F(1),F(0)
    for x in xs: result=mul(result,x)
    return result

def main() -> None:
    rng=Random(369)
    for n in range(10):
        for _ in range(1000):
            factors=[(F(rng.randint(-12,12), rng.randint(1,12)),
                      F(rng.randint(-12,12), rng.randint(1,12))) for j in range(n)]
            weight=F(1)
            for g in factors: weight*=norm(g)
            assert norm(prod(factors))==weight
            assert norm(prod([conj(g) for g in factors]))==weight
            assert norm(prod([(F(0),F(1))]+factors))==weight
    assert norm(prod([(F(0),F(0))])) == 0
    assert norm(prod([(F(0),F(1))])) == 1
    print("PASS: 10000 exact rational complex gamma-list Born product tests")
    print("PASS: 10000 conjugation and phase-i invariance tests")
    print("PASS: nonzero and zero-amplitude edge cases")
    print("NOTE: selected physical gamma_j and original 2017 Eq.(25) remain open")

if __name__=="__main__":
    main()
