#!/usr/bin/env python3
"""Exact Schur increment controls for MCG array detection. NOT physical validation.

Prior art: block covariance GLS; DASHI psychotronics_field_loom_covariance.py;
DiamondMCGFiniteBridgeExact and existing finite complex Cauchy-Schwarz.
"""
import sympy as sp

def same(a,b):
    if isinstance(a,sp.MatrixBase):
        assert a.shape==b.shape
        for d in a-b: assert sp.cancel(d)==0,sp.factor(d)
    else:
        assert sp.cancel(a-b)==0,sp.factor(a-b)

def test(n):
    # Rational positive-definite covariance L L^T, nonuniform source response.
    L=sp.eye(n+1)
    for i in range(n+1):
        L[i,i]=sp.Rational(i+2,2)
        for j in range(i):
            L[i,j]=sp.Rational((i+2*j+1)%5-2,7)
    C=L*L.T
    old=C[:n,:n]; c=C[:n,n]; d=C[n,n]
    s=sp.Matrix([sp.Rational(((-1)**i)*(i+2),i+3) for i in range(n)])
    t=sp.Rational(3,5)
    response=s.col_join(sp.Matrix([t]))
    old_info=(s.T*old.inv()*s)[0]
    new_info=(response.T*C.inv()*response)[0]
    innovation=t-(c.T*old.inv()*s)[0]
    schur=d-(c.T*old.inv()*c)[0]
    assert schur>0
    same(new_info-old_info,innovation**2/schur)
    residual=old.inv()*c
    blockinv=old.inv().row_join(sp.zeros(n,1)).col_join(sp.zeros(1,n+1))
    vec=residual.col_join(sp.Matrix([-1]))
    blockinv+=vec*vec.T/schur
    same(C.inv(),blockinv)
    # Negative control: new cardiac signal predicted entirely by old channels.
    redundant=(c.T*old.inv()*s)[0]
    r0=s.col_join(sp.Matrix([redundant]))
    same((r0.T*C.inv()*r0)[0],old_info)
    print(f'PASS n={n}: conditional innovation, Schur inverse, zero-gain control')

def symbolic_two_channel():
    v,w,k,x,y=sp.symbols('v w k x y',real=True)
    C=sp.Matrix([[v,k],[k,w]])
    z=sp.Matrix([x,y])
    same((z.T*C.inv()*z)[0]-x*x/v,
         (y-k*x/v)**2/(w-k*k/v))
    P=sp.eye(2)-sp.ones(2,2)/2
    same(P*sp.ones(2,1),sp.zeros(2,1))
    same((P*z).dot(P*z),(x-y)**2/2)
    print('PASS symbolic 2-channel conditional gain and common-mode loss')

if __name__=='__main__':
    symbolic_two_channel()
    for n in [1,2,3,4,6,10]: test(n)
    print('PASS exact rational regressions; Agda all-N and physical covariance OPEN')
