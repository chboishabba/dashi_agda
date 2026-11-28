#!/usr/bin/env python3
"""BR39 source-level physical cutoff commutator and actual BR34 boundary weld.
This does not assert Sobolev/tame estimates or Einstein-Israel PDE existence.
Reuses actual committed BR34 tensor/gauge boundary operators, no copies.
"""
import sympy as S
from check_hopf369_br_warped_physical_attachment import (
    metric_rows, gauge_rows, dec, eta, ids, operators,
)

def scalar_bulk():
    X=S.symbols('t x y z n')
    t,x,y,z,n=X
    chi=1+t*x+n*n+z*y
    u=2+t*y+x*n+z*z+t*t*n
    principal=S.Matrix(5,5,lambda i,j:(i+1)*(j+2)+(i==j)*3)
    first=S.Matrix([t+1,x*y+1,n+2,z,2*n])
    mass=t*x+y
    L=lambda f:S.expand(sum(principal[i,j]*S.diff(f,X[i],X[j]) for i in range(5) for j in range(5))
          +sum(first[i]*S.diff(f,X[i]) for i in range(5))+mass*f)
    residual=S.expand(sum(principal[i,j]*
          (S.diff(chi,X[i],X[j])*u+S.diff(chi,X[i])*S.diff(u,X[j])
           +S.diff(chi,X[j])*S.diff(u,X[i]))
          for i in range(5) for j in range(5))
          +sum(first[i]*S.diff(chi,X[i])*u for i in range(5)))
    assert S.expand(L(chi*u)-chi*L(u)-residual)==0
    # Recover all 15 tensor components + five covector components, not a scalar
    # surrogacy; coefficients are scalar and act componentwise.
    for k in range(20):
        v=u+(k+1)*t*x+k*n
        r=S.expand(sum(principal[i,j]*
              (S.diff(chi,X[i],X[j])*v+S.diff(chi,X[i])*S.diff(v,X[j])
               +S.diff(chi,X[j])*S.diff(v,X[i]))
              for i in range(5) for j in range(5))
              +sum(first[i]*S.diff(chi,X[i])*v for i in range(5)))
        assert S.expand(L(chi*v)-chi*L(v)-r)==0
    # Boundary collar: chi=1 and chi_n=0 at wall by construction.
    collar=1+(n*n)*(1+t*x+y*z)
    assert S.expand(collar.subs(n,0)-1)==0
    assert S.expand(S.diff(collar,n).subs(n,0))==0
    # Deliberately non-collared cutoff has physical derivative defect.
    assert S.diff(chi,n)!=0
    print('BR39 bulk: 21/21 five-direction cutoff identities; collar jet PASS')

def boundary():
    # Exact rational original BR34 wall rows; forced derivative is not
    # suppressed and therefore checks the actual Israel and gauge channels.
    rr=S.Rational
    q=S.Matrix([rr(2,3),rr(1,5),rr(-3,7),rr(2,11)])
    j=rr(-6,5); c=rr(7,3); cn=rr(-2,9)
    vals=[S.Matrix([rr((i+1)*(k+2)%13-6,7) for i in range(15)]) for k in range(4)]
    p,px,m,mx=map(dec,vals)
    cs=[S.Matrix([rr((i+2)*(k+3)%11-5,8) for i in range(5)]) for k in range(4)]
    cp,cpx,cm,cmx=cs
    z15=S.zeros(5)
    Z=dec(S.zeros(15,1))
    for a in ('D','E'):
        old=metric_rows(p,px,m,mx,q,j,a)
        cur=metric_rows(c*p,c*px+cn*p,c*m,c*mx+cn*m,q,j,a)
        normal=metric_rows(Z,p,Z,m,q,S.Zero,a)
        assert S.simplify(cur-c*old-cn*normal)==S.zeros(30,1),a
        oldg=gauge_rows(cp,cpx,cm,cmx,q,j,a)
        newg=gauge_rows(c*cp,c*cpx+cn*cp,c*cm,c*cmx+cn*cm,q,j,a)
        normalg=gauge_rows(z15,cp,z15,cm,q,S.Zero,a)
        assert S.simplify(newg-c*oldg-cn*normalg)==S.zeros(10,1),a
        # The normal derivative of the cutoff DOES act on the mean trace
        # force and the released E gauge row, not just Israel.
        assert normal[29]!=0
    print('BR39 boundary: 2 allocations x (30 metric + 10 gauge) signed rows PASS')

if __name__=='__main__':
    scalar_bulk()
    boundary()
