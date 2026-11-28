"""Exact-rational midpoint differentiation and a posteriori residual enclosure.

The existing Cayley stage is differentiated on its original signed chart.
No finite-difference replacement of the tangent and no continuum claim.
"""
import sympy as s

def tangent(A,x,b,h,dA,dx,db):
    I=s.eye(A.rows)
    y=(I-h*A/2).inv()*((I+h*A/2)*x+h*b)
    mid=(x+y)/2
    dy=(I-h*A/2).inv()*((I+h*A/2)*dx+h*dA*mid+h*db)
    return y,dy

def residual_bound(A,x,y,b,h):
    """For dissipative exact A, inverse of I-h*A/2 has norm <= 1.
    L1 residual is rational upper bound for Euclidean error, no sqrt rounding.
    Inputs are exact rationals, not unverified floating center states.
    """
    assert all(v.is_Rational for v in list(A)+list(x)+list(y)+list(b)+[h])
    assert h>0 and (-(A+A.T)).is_positive_semidefinite
    r=(s.eye(A.rows)-h*A/2)*y-(s.eye(A.rows)+h*A/2)*x-h*b
    return sum(abs(v) for v in r)

def fixtures():
    t=s.symbols('t', real=True); h=s.Rational(1,3)
    A=s.Matrix([[-2-t,3],[-3,-1]])
    x=s.Matrix([1+t,2-t]); b=s.Matrix([t,0])
    y,dy=tangent(A,x,b,h,A.diff(t),x.diff(t),b.diff(t))
    assert all(s.cancel(v)==0 for v in dy-y.diff(t))
    m=(x+y)/2
    assert s.cancel((y.dot(y)-x.dot(x))/2-h*m.dot(A*m+b))==0
    a=A.subs(t,s.Rational(1,2)); xx=x.subs(t,s.Rational(1,2)); bb=b.subs(t,s.Rational(1,2))
    yy=y.subs(t,s.Rational(1,2))
    for j in range(1,22):
        z=yy+s.Matrix([s.Rational(j,1000),-s.Rational(j,2000)])
        bound=residual_bound(a,xx,z,bb,h)
        assert (z-yy).dot(z-yy)<=bound**2
    rejected=False
    try:residual_bound(s.eye(2),xx,yy,bb,h)
    except AssertionError:rejected=True
    assert rejected
    return dict(symbolic_tangent=True,energy_identity=True,rational_residual_cases=21,active_negative_control=True)
if __name__=='__main__':
    print(fixtures())
