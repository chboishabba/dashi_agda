#!/usr/bin/env python3
"""BR36: exact complex Lorentz chart and D -> E row replacement.
Uses BR34 frozen reference owners. No variable-coefficient claim.
"""
import sympy as s

eta=s.diag(-1,1,1,1)

def boost(a,v):
    """a=z0/ell, v=z_sp/ell; v.T*v=a*a-1; a+1 nonzero."""
    return s.Matrix([[a]]).row_join(v.T).col_join(
        v.row_join(s.eye(3)+v*v.T/(1+a)))

def check():
    # Rational parametrization of complex unit timelike covectors.
    # The identities are exact on a dense chart, with explicit denominator.
    w=s.Matrix(s.symbols('w1:4'))
    r=w.dot(w)
    a=(1+r)/(1-r); v=2*w/(1-r)
    B=boost(a,v)
    assert (B.T*eta*B-eta).applyfunc(s.cancel)==s.zeros(4)
    assert (B*boost(a,-v)-s.eye(4)).applyfunc(s.cancel)==s.zeros(4)
    assert (B[:,0]-s.Matrix([a,*v])).applyfunc(s.cancel)==s.zeros(4,1)
    # Exact row substitution inverse: E replaces one D row.
    # x0=B_D^-1 f0; h=B_D^-1 e_r. E solution x=x0+h t,
    # t=(target-newrow*x0)/(newrow*h).
    n=5
    A=s.Matrix([[2,1,0,0,0],[1,3,1,0,0],[0,1,4,1,0],[0,0,1,5,1],[0,0,0,1,6]])
    f=s.Matrix(s.symbols('f0:5')); row=s.Matrix(1,n,s.symbols('g0:5')); target=s.Symbol('target')
    for i in range(n):
        e=s.eye(n)[:,i]; h=A.inv()*e; x0=A.inv()*f
        den=(row*h)[0]; x=x0+h*(target-(row*x0)[0])/den
        E=A.copy(); E[i,:]=row; rhs=f.copy(); rhs[i]=target
        assert (E*x-rhs).applyfunc(s.cancel)==s.zeros(n,1)
        assert s.cancel(E.det()-A.det()*den)==0
    # At BR33 flat metric, response to unit temporal gauge jump:
    # p=-div(g)/q = z0/q, n_minus=-C*p (n_plus=0,F=0).
    # Gauge: response to unit temporal covector jump gives C_n^- = z0/(T+2j).
    # Nonzero in damped chart; actual warped denominators must be checked.
    z0,q,C,T,j=s.symbols('z0 q C T j', nonzero=True)
    assert s.cancel((-C*z0/q)/z0+C/q)==0
    assert s.cancel((z0/(T+2*j))/z0-1/(T+2*j))==0
    print('PASS exact Lorentz chart, inverse and 5 rank-one row replacement identities')
    print('Flat D-to-E denominators retained; actual warped E denominator requires estimate.')

if __name__=='__main__':check()
