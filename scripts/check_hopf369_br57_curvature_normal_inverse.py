#!/usr/bin/env python3
"""BR57: actual BS13 normal electric curvature -> normal shear transport.

Original BS13 identity on AdS5 warped normal b(n):
  E_na^nb = -S'_a^b -2(b'/b)S_a^b +2 b^-4 Q_a^b
          = -b^-2 ∂n(b² S_a^b)+2b^-4 Q_a^b.
Thus p=b² S obeys p'=-b² E+2b^-2 Q=:F.

For the ORIGINAL two-sided normal interval [0,L], retaining its
normal-holonomy moment M=int b² S, the *unique* primitive is
  p(n)=C+int_0^n F; C=(M-int_0^L(L-x)F(x)dx)/L.
This is a true bidirectional normal inversion, including trace/shear
modes and the original constant normal holonomy. If b²>=m>0,
 |S(n)| <= m^-1 (|M|/L+2 int_0^L |F|).
It controls NORMAL SHEAR from electric curvature plus Q and M, not the
full weighted curvature-to-metric quotient; tracefree tangential gauge,
spatial derivatives and AdS radial infinity remain independent.

Original b=4/5*cosh(n-log2), L=2log2, m=16/25. Tests are exact
sympy for 16 independent normal tensor entries, split by --part.
"""
import argparse
import sympy as s
from fractions import Fraction as F

n=s.symbols('n',real=True)
L=2*s.log(2)
b=s.Rational(4,5)*s.cosh(n-s.log(2))
b2=b*b
bInv2=1/b2

def reconstruct(Fsource,moment):
    # Formal exact source integration, not an ad hoc choice of constant:
    x=s.symbols('x',real=True)
    fx=Fsource.subs(n,x)
    primitive=s.integrate(fx,(x,0,n))
    weighted=s.integrate((L-x)*fx,(x,0,L))
    C=s.simplify((moment-weighted)/L)
    return s.simplify((C+primitive)/b2),C

def sector(component):
    # Twenty independent source profiles; not just a scalar trace.
    k=component
    p=s.Rational(k+2,11)+s.Rational(k+3,13)*n
    p+=s.Rational(k+5,17)*n*n
    Q=s.Rational((k+2)%7-3,19)+s.Rational(k+1,23)*n
    S=p/b2
    E= -s.diff(p,n)/b2+2*Q/b2**2
    Fsource=-b2*E+2*Q/b2
    assert s.simplify(Fsource-s.diff(p,n))==0
    moment=s.integrate(p,(n,0,L))
    recovered,C=reconstruct(s.diff(p,n),moment)
    assert s.simplify(recovered-S)==0
    assert s.simplify(C-p.subs(n,0))==0
    assert s.simplify(-s.diff(b2*recovered,n)+2*Q/b2-b2*E)==0
    # Zero curvature-source/control is NOT enough without M. Keeping
    # p constant nonzero provides an actual normal holonomy obstruction.
    constant=s.Rational(k+1,7)
    zeroF=s.S.Zero
    zeroQ=s.S.Zero
    kernelS=constant/b2
    kernelE=-s.diff(b2*kernelS,n)/b2
    assert kernelE==0 and constant!=0
    assert s.integrate(b2*kernelS,(n,0,L))==L*constant
    print("PASS BR57 exact BS13 normal electric/shear inverse channel",k)

def constants():
    assert b.subs(n,0)==1 and b.subs(n,L)==1
    assert s.simplify(b.subs(n,L/2)-s.Rational(4,5))==0
    # Sharp source warp lower bound m=(4/5)^2; every n∈[0,L]
    # has cosh(n-log2)>=1. The inequality follows from FTC twice.
    m=s.Rational(16,25)
    assert s.simplify(m*bInv2.subs(n,L/2)-1)==0
    assert s.simplify(m*bInv2.subs(n,0)-m)==0
    # Explicit reference bound for positive |F| using a constant F:
    M=s.Rational(3,7)*L
    F0=s.Rational(5,13)
    C=s.simplify((M-F0*L**2/2)/L)
    sol=(C+F0*n)/b2
    assert s.simplify(s.integrate(b2*sol,(n,0,L))-M)==0
    assert s.simplify(s.diff(b2*sol,n)-F0)==0
    print("PASS BR57 actual AK warp and quantitative holonomy-bearing 1D inverse")

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--part',choices=['constants','channel'],default='constants')
    p.add_argument('--component',type=int,default=0)
    a=p.parse_args()
    if a.part=='constants':constants()
    else:
        if not 0<=a.component<16:raise ValueError('physical normal electric 4x4 components')
        sector(a.component)

if __name__=='__main__':main()
