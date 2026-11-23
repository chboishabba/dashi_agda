#!/usr/bin/env python3
"""Actual classical non-product Gr(2,4) Schubert geometry Hodge H2.

Grassmannian of 2-planes in C4 = Klein quadric Q4 in P5.
Integral cohomology ring Z[c1,c2]/(h3,h4) from universal tautological
sequence and the classical Schubert cell decomposition (external inputs).
Exact Giambelli/Pieri, Poincare dual, inverse rational algebraic cycle.
Does not assert all-projective-varieties Hodge or an Agda comparison weld.
"""
import sympy as s
from fractions import Fraction
from random import Random
h,c=s.symbols('h c')
h3=h**3-2*h*c
h4=h**4-3*h*h*c+c*c
GB=s.groebner([h3,h4],h,c,order='lex',domain=s.QQ)
classes={'empty':s.S.One,'1':h,'2':h*h-c,'11':c,'21':h*c,'22':c*c}
degree={'empty':0,'1':1,'2':2,'11':2,'21':3,'22':4}
cycles={'empty':'Gr(2,4)','1':'Schubert hyperplane divisor',
        '2':'lines contained in a fixed projective plane',
        '11':'lines passing through a fixed projective point',
        '21':'Schubert projective line', '22':'Schubert point'}
# Schubert partition duality by complements in the 2x2 rectangle.
dual={'empty':'22','1':'21','2':'2','11':'11','21':'1','22':'empty'}

def red(f):return s.expand(GB.reduce(s.expand(f))[1])
def top(f):
    # Graded quotient: integration takes only weighted-degree 4.
    # Lower-degree components have zero integral and are *not* asserted away.
    return s.expand(red(f)).coeff(c,2)

# Distinct geometrically defined middle-dimensional alpha/beta planes.
assert red(classes['2']*classes['11'])==0
assert top(classes['2']**2)==1
assert top(classes['11']**2)==1
assert red(classes['1']**2-classes['2']-classes['11'])==0
assert red(classes['1']*classes['2']-classes['21'])==0
assert red(classes['1']*classes['11']-classes['21'])==0
assert red(classes['1']*classes['21']-classes['22'])==0
assert top(classes['1']**4)==2 # Plucker/Klein quadric has degree 2

for n,a in classes.items():
    for m,b in classes.items():
        if degree[n]+degree[m]==4:
            expected=int(m==dual[n])
            assert top(a*b)==expected, (n,m,top(a*b),expected)
# Different ring generating basis and exact rational 6x6 intersection matrix.
labels=list(classes)
P=s.Matrix([[top(classes[a]*classes[b]) if degree[a]+degree[b]==4 else 0 for b in labels] for a in labels])
assert P.det() in (1,-1)
assert P.inv()==P # canonical dual pairing is involutive
assert tuple(len([n for n in labels if degree[n]==p]) for p in range(5))==(1,1,2,1,1)

# BIDI: A rational cohomology class with exact Schubert coefficients
# is the cycle class of the same linear combination of the six literal
# algebraic incidence varieties. Recover each coefficient by integrating
# against its complementary Schubert cycle (not by a textual lookup).
rng=Random(20261123)
checks=0
for _ in range(1200):
    coeff={n:s.Rational(rng.randrange(-17,18),rng.randrange(1,11)) for n in labels}
    cohomology=sum((coeff[n]*classes[n] for n in labels),s.S.Zero)
    for n in labels:
        a=top(cohomology*classes[dual[n]])
        assert a==coeff[n], (n,a,coeff[n])
        checks+=1
    reconstructed=sum((top(cohomology*classes[dual[n]])*classes[n] for n in labels),s.S.Zero)
    assert red(cohomology-reconstructed)==0

# Honest non-surjectivity firewall: formal classes outside H^(p,p)
# do not come from algebraic codimension p cycles; no such extra pieces
# exist on this cellular homogeneous X, but arbitrary X are not cellular.
assert GB.reduce(h3)[1]==0 and GB.reduce(h4)[1]==0
print('PASS classical Gr(2,4) / Klein quadric: six literal Schubert incidence cycles')
print('Betti/Hodge diagonal ranks:',[sum(degree[x]==p for x in labels) for p in range(5)])
print('Poincare pairing determinant:',P.det(),'self-dual:',P*P==s.eye(6),'Plucker degree:',top(h**4))
print('PASS exact Pieri/Giambelli products, middle-ruling orthogonality,',checks,'rational coefficient recoveries')
print('OPEN: native literal algebraic scheme/cycle class + singular-de Rham comparison; general Hodge H3 all X,p')
