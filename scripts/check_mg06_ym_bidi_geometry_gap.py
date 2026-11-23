#!/usr/bin/env python3
"""Finite exact spatial/time covariance non-transport diagnostic.

Do not confuse this explicit positive anisotropic covariance model with
physical Wilson/Gibbs source or a proof about 4D Yang-Mills.
"""
from fractions import Fraction as F
from itertools import product
import sympy as S

def ar_cov(q):
    return S.Matrix([[S.Rational(1),S.Rational(q.numerator,q.denominator)],
                     [S.Rational(q.numerator,q.denominator),S.Rational(1)]])

def main():
    space=F(1,2)
    for n in (3,7,31,127):
        temporal=F(n,n+1)
        # Four lattice sites (x,t) in {0,1}²: positive Gaussian covariance.
        kernel=S.kronecker_product(ar_cov(space),ar_cov(temporal))
        assert kernel.shape==(4,4)
        assert all(z>0 for z in kernel.eigenvals())
        # Extend by the standard product of positive AR(1) covariance kernels.
        for distance,time in product(range(1,6),repeat=2):
            c=space**distance*temporal**time
            assert 0<c<=space**distance
            assert temporal**time > space**time
        assert F(1)-temporal==F(1,n+1)
        print(f'PASS n={n}: positive covariance; spatial={space}, temporal={temporal}, temporal gap={1-temporal}')
    site_a=(0,0)
    site_b=(0,5)
    spatial_distance=lambda a,b:abs(a[0]-b[0])
    temporal_distance=lambda a,b:abs(a[1]-b[1])
    assert spatial_distance(site_a,site_b)==0 and temporal_distance(site_a,site_b)==5
    print('PASS observer projection loses physical-time separation')
    print('OPEN original Wilson measure, uniform CMP116 spatial+time shell bound, E1/OS and dense physical spectrum')

if __name__=='__main__':main()
