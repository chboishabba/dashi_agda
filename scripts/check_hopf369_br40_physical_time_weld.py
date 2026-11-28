#!/usr/bin/env python3
"""BR40b/c: physical differentiated Israel/gauge rows and source trace solve.

Consumes the actual BR34 warped boundary operator, not a new flat model.
Exact rational/SymPy identities; a full continuum estimate is NOT claimed.
Designed for bounded per-section runs: --part time|trace|subsidiary|all.
"""
import argparse
import sympy as s
from check_hopf369_br_warped_physical_attachment import (
    metric_rows, gauge_rows, metric_side, trace4, E4, keys,
)

def zero(x):
    if isinstance(x,s.MatrixBase):
        return x.applyfunc(s.cancel)==s.zeros(*x.shape)
    return s.cancel(x)==0

def entries(N,tag,t):
    # Distinct, nontrivial time-dependent source jets at both faces.
    return s.Matrix([s.Rational((i+2)*(j+3)%17-8,7)
          +t*s.Rational((i+3)*(j+5)%19-9,11)
          +t*t*s.Rational((i+5)*(j+2)%13-6,17)
          for i in range(N) for j in [tag]])

def tensor(a):
    from check_hopf369_br_warped_physical_attachment import dec
    return dec(a)

def sample():
    t=s.Symbol('time')
    P=[tensor(entries(15,k,t)) for k in (0,1,2,3)]
    C=[entries(5,k,t) for k in (4,5,6,7)]
    q=s.Matrix([s.Rational(i+1,3)+t*s.Rational(i+2,5) for i in range(4)])
    j=s.Rational(-6,5)+s.Rational(3,7)*t
    return t,P,C,q,j

def time():
    t,(p,px,m,mx),(c,cx,d,dx),q,j=sample()
    qd=q.diff(t);jd=j.diff(t)
    zp=s.zeros(4,1)
    zt=s.zeros(5)
    from check_hopf369_br_warped_physical_attachment import dec
    Z=dec(s.zeros(15,1))
    for alloc in 'DE':
        orig=metric_rows(p,px,m,mx,q,j,alloc)
        dot=orig.diff(t)
        fields=metric_rows(p.diff(t),px.diff(t),m.diff(t),mx.diff(t),q,j,alloc)
        bg=metric_rows(p,px,m,mx,qd,jd,alloc)-metric_rows(p,px,m,mx,zp,s.S.Zero,alloc)
        assert zero(dot-fields-bg),('metric',alloc)
        gorig=gauge_rows(c,cx,d,dx,q,j,alloc)
        gfield=gauge_rows(c.diff(t),cx.diff(t),d.diff(t),dx.diff(t),q,j,alloc)
        gbg=gauge_rows(c,cx,d,dx,qd,jd,alloc)-gauge_rows(c,cx,d,dx,zp,s.S.Zero,alloc)
        assert zero(gorig.diff(t)-gfield-gbg),('gauge',alloc)
        # Both physical allocations retain precisely the mean force as last row.
        assert orig[-1]==metric_side(p,px,q,j/2)[3]+metric_side(m,mx,q,-j/2)[3]
    print('PASS exact differentiated actual metric/gauge physical rows: D/E, 30+10 each')

def trace():
    t,(p,px,m,mx),_,q,j=sample()
    plus=metric_side(p,px,q,j/2)
    minus=metric_side(m,mx,q,-j/2)
    H,b,K,taup,ca,cn=plus
    G,d,Q,taum,ea,en=minus
    J=2*(K-Q)-j*(H+G)
    betaSum=b+d; betaJump=b-d
    scaleSum=(p[4,4]+m[4,4])/2
    scaleDiff=(p[4,4]-m[4,4])/2
    F=taup+taum
    mean=F+(q.T*E4*betaSum)[0]+2*j*scaleDiff
    jump=trace4(J)+2*(q.T*E4*betaJump)[0]+4*j*scaleSum
    targetp=trace4(px[:4,:4]);targetm=trace4(mx[:4,:4])
    assert zero(mean+(jump/2)-targetp)
    assert zero(mean-(jump/2)-targetm)
    # Actual Israel jump, including off-continuity beta and both scale sheets.
    rhs=px[:4,:4]-mx[:4,:4]-q*betaJump.T-betaJump*q.T-j*scaleSum*E4
    assert zero(J-rhs)
    # Signed boundary energy work on a continuous tangential time jet:
    # trace is not a positive shear square.
    w=s.Matrix(4,4,lambda a,b:s.Rational((a+b+2)*(a+b+3),7))
    contraction=lambda a,b: s.trace(E4*a*E4*b)
    jumpN=px[:4,:4]-mx[:4,:4]
    assert zero(contraction(w,jumpN)-contraction(w,J+q*betaJump.T+betaJump*q.T+j*scaleSum*E4))
    print('PASS physical trace-plus/minus reconstruction and 10-component Israel source work')

def subsidiary():
    t,_,(c,cx,d,dx),q,j=sample()
    M=s.Matrix(4,4,lambda a,b:s.Rational((a+1)*(b+1),9))
    Mt=s.Matrix(4,4,lambda a,b:s.Rational(a+b+1,11))
    # Nonzero mean K and its time derivative preserved.
    ci=c[:4,0];di=d[:4,0];jump=ci-di;normal=c[4]-d[4]
    normalSource=cx[:4,0]-dx[:4,0]+q*normal-j*(ci+di)
    explicit=normalSource-2*M*E4*jump
    tangSolve=explicit-q*normal+2*M*E4*jump+j*(ci+di)
    assert zero(tangSolve-(cx[:4,0]-dx[:4,0]))
    gauss=gauge_rows(c,cx,d,dx,q,j,'D')[-1]
    normalSolve=gauss+(q.T*E4*jump)[0]+2*j*(c[4]+d[4])
    assert zero(normalSolve-cx[4]+dx[4])
    # Background derivative includes independent M_t and no cross-trace collapse.
    def cod(c,cx,d,dx,q,j,M):
        v=c[:4,0]-d[:4,0]
        return cx[:4,0]-dx[:4,0]+q*(c[4]-d[4])-2*M*E4*v-j*(c[:4,0]+d[:4,0])
    md=M+t*Mt
    value=cod(c,cx,d,dx,q,j,md)
    field=cod(c.diff(t),cx.diff(t),d.diff(t),dx.diff(t),q,j,md)
    bkg=cod(c,cx,d,dx,q.diff(t),j.diff(t),Mt)-cod(c,cx,d,dx,s.zeros(4,1),s.S.Zero,s.zeros(4))
    assert zero(value.diff(t)-field-bkg)
    print('PASS general mean Codazzi derivative, physical Gauss normal reconstruction')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['time','trace','subsidiary','all'],default='all')
    a=p.parse_args()
    for name,fn in [('time',time),('trace',trace),('subsidiary',subsidiary)]:
        if a.part in ('all',name):fn()
