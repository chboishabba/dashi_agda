#!/usr/bin/env python3
"""Exact factor-fibred circle-phase transport and query-indexed nonfactorability.
DASHI primary owner: ConsumerIndexedResidualRefinementExact,\nBidiResidualApproximationExact; supporting nonfactorability via\nIntersectionalNonFactorability, QueryIndexedProjectionAdequacyExact,
BalancedTernaryC2C3DihedralCodecBridgeExact, WaveAlgorithmLift.
All phases are rational test fixtures; no claim about alpha=1/(2*pi).
"""
from fractions import Fraction

def split_c3(x):
    x=x%1
    j=(3*x).__floor__()
    return j,x-Fraction(j,3)

def assemble(j,r): return (Fraction(j,3)+r)%1
def mul_phase(m,x): return m*x%1
def sign(x):
    x=x%1
    if x==0 or x==Fraction(1,2): return 0
    return 1 if x<Fraction(1,2) else -1

def transport(j,r,m):
    return split_c3(m*assemble(j,r))

def audit():
    phases=[Fraction(i,120) for i in range(120)]
    factors=(9,11)
    for phase in phases:
        j,r=split_c3(phase)
        assert assemble(j,r)==phase
        for m in (2,3,9,11,99):
            j2,r2=transport(j,r,m)
            assert assemble(j2,r2)==mul_phase(m,phase)
            assert 0<=r2<Fraction(1,3)
        u=transport(*transport(j,r,9),11)
        v=transport(*transport(j,r,11),9)
        assert u==v
        assert assemble(*u)==mul_phase(99,phase)
    # Both lie in the middle C3 sector, but opposite sine sign:
    x,y=Fraction(5,12),Fraction(7,12)
    assert split_c3(x)[0]==split_c3(y)[0]==1
    assert sign(x)==1 and sign(y)==-1
    # Even with a fixed phase action, coarse C3 sector is not sufficient.
    for m in (1,3,9,11):
        pair=None
        for x in phases:
            for y in phases:
                if split_c3(x)[0]==split_c3(y)[0] and sign(mul_phase(m,x))!=sign(mul_phase(m,y)):
                    pair=(x,y);break
            if pair:break
        assert pair is not None
        print('C3 fails query after multiplier',m,'witness',pair)
    print('PASS: exact factor-order commute, retained residual, signed-query non-descent')
    print('BOUNDARY: symbolic rational fibration; not an efficient oracle for real pi phase')

if __name__=='__main__': audit()
