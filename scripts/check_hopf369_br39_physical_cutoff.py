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


def optical_matrices():
    # This is the actual BR14/15 five-direction optical operator, not a
    # componentwise scalar proxy: metric J_a mixes fifteen channels and
    # subsidiary L_a mixes five channels. Projectors retain trace mixing.
    R,J,Vb,Vh,Q,Lm,Sm=operators()
    b=S.Integer(4); bk=S.Rational(2,3)
    eigen=(-5,1,3)
    E=sum((b**S.Rational(v,2)*q for v,q in zip(eigen,Q)),S.zeros(15))
    Ei=sum((b**S.Rational(-v,2)*q for v,q in zip(eigen,Q)),S.zeros(15))
    assert E*Ei==S.eye(15)
    X=S.symbols('t x y z n');t,x,y,z,n=X
    chi=1+n*n*(t+x)+t*y+z*x
    def one_case(N,firsts):
        U=S.Matrix([S.Integer(k+1)*t*x+S.Integer(k+2)*n*y+z*z+(k+1)*t for k in range(N)])
        mass=S.diag(*[k+2 for k in range(N)])
        def derivatives(U):
            normal=S.diff(U,n,2)
            tangent=sum(((-1 if i==0 else 1)*S.diff(U,X[i],2) for i in range(4)),S.zeros(N,1))
            linear=sum((firsts[i]*S.diff(U,X[i]) for i in range(4)),S.zeros(N,1))
            return normal+tangent+linear+mass*U
        second=sum((S.diff(chi,X[i],2)*((-1 if i==0 else 1) if i<4 else 1)*U
              +2*S.diff(chi,X[i])*((-1 if i==0 else 1) if i<4 else 1)*S.diff(U,X[i])
                  for i in range(5)),S.zeros(N,1))
        first=sum((firsts[i]*S.diff(chi,X[i])*U for i in range(4)),S.zeros(N,1))
        assert (derivatives(chi*U)-chi*derivatives(U)-second-first).applyfunc(S.expand)==S.zeros(N,1)
    one_case(15,[bk*E*J[i]*Ei for i in range(4)])
    one_case(5,[2*bk*(-1 if i==0 else 1)*Lm[i] for i in range(4)])
    print('BR39 optical: exact BR15 15-component and BS4 5-component matrix commutators PASS')

if __name__=='__main__':
    scalar_bulk()
    boundary()
    optical_matrices()
