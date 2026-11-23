"""Conditional scalar extension audit, not a source class receipt."""
import sympy as s
from itertools import product
u=s.Symbol('u'); mod=s.cyclotomic_poly(12,u)
red=lambda x:s.rem(s.expand(x),mod,u)
I=s.eye(3); z=u**4; i=u**3
F=s.Matrix(3,3,lambda a,b:z**((a*b)%3)); G=s.Matrix(3,3,lambda a,b:z**((-a*b)%3)); P=s.Matrix(3,3,lambda a,b:int(a==(-b)%3))
M=lambda X:X.applyfunc(red)
assert red(i*i)==-1 and red(z*z+z+1)==0
assert M(F*F)==3*P and M(G*G)==3*P
# Use unnormalized one-axis model; equalities scaled by 3.
assert M((i*F)**2)==-3*P
assert M((i*F)*(-i*G))==3*I
# Scalar extension on paired sectors: opposite i gauges required for a plain swap.
assert M((-i*G)*(i*F))==3*I
assert M((i*G)*(i*F))==-3*I
# Enumerate C4 spectrum, real quarter trace optional (not assumed for source).
def spectra(half):
    for a in range(91):
        for b in range(91-a):
            for c in range(91-a-b):
                d=90-a-b-c
                if a-b+c-d==half:yield a,b,c,d
for h in (-90,66):
    rows=list(spectra(h)); assert rows
    assert all(sum(x)==90 for x in rows)
    print('half trace',h,'C4 spectra',len(rows),'quarter traces',len({(a-c,b-d) for a,b,c,d in rows}))
    if h==-90: assert all(a==c==0 for a,b,c,d in rows)
    else: assert all(a+c==78 and b+d==12 for a,b,c,d in rows)
print('PASS SymPy Phi12 scalar extension, paired mirror gauge, conditional C4 spectra; no class selection')
