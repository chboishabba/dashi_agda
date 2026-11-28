#!/usr/bin/env python3
"""BS11: full reference normal-holonomy reduction, independent Ricci checks.
Consumes BS6/7 and BS10 covariant derivatives. Classical linear geometry only.
"""
import sympy as s
import check_hopf369_bs_physical_modes as five
import check_hopf369_bs_york_resonance as four


def run():
    n,b,k=five.n,five.b,five.k
    # Align independent base coordinates: both modules use the same symbols.
    t,x,y,r=five.t,five.x,five.y,five.r
    h=four.h; hi=four.hi; c=four.c
    assert tuple(four.x)==(t,x,y,r)
    f=n+n*n; chi=t*x+r*r+y*r
    A=s.Matrix([r*t+x*y, t*r+x*x, x*r+t*y, r*r+t*x])
    M=s.Matrix(4,4,lambda i,j:(i+j+1)*r+(i+1)*(j+1)*t*x+int(i==j)*y*y)
    T=f*M
    tr=s.trace(hi*T); W=four.divt(T)-four.grad(tr)
    divA=four.divv(A)
    phi=-2*chi/b**2
    beta=A/b**4
    p=s.zeros(5); p[0,0]=2*phi
    p[0,1:5]=(b*b*beta).T; p[1:5,0]=b*b*beta
    p[1:5,1:5]=b*b*T+2*chi*h
    E=five.linE(p)
    P=four.box(A,1)-3*c*A-four.grad(divA)
    expected_mixed=W.diff(n)/2-P/(2*b**4)
    assert all(five.simp(E[0,i+1]-expected_mixed[i])==0 for i in range(4))
    F=four.box0(chi)-4*c*chi
    sigma=tr.diff(n)/2-divA/b**4
    expected_normal=-sigma.diff(n)-2*k*sigma+2*F/b**4
    assert five.simp(E[0,0]-expected_normal)==0
    # Arbitrary pure relative tangential tensor: trace of the tangential E.
    p=s.zeros(5);p[1:5,1:5]=b*b*T
    E=five.linE(p)
    trace=s.trace(hi*E[1:5,1:5])/b**2
    expected=(four.divv(W)+3*c*tr)/b**2-tr.diff(n,2)/2-4*k*tr.diff(n)
    assert five.simp(trace-expected)==0
    # Divergence Proca identity forces transverse holonomy, no division by Box.
    assert four.clean(four.divv(P)+6*c*divA)==0
    V=s.Matrix([r*t,t*x,r*y,x*x]); LV=four.L(V)
    WV=four.divt(LV)-four.grad(s.trace(hi*LV))
    assert four.zero(WV-(four.box(V,1)-3*c*V-four.grad(four.divv(V))))
    # Normal transport: xi vanishes at both faces by chosen scalar mean;
    # V vanishes at both by chosen vector mean. Exact polynomial fixture
    # for arbitrary profiles (the integral definitions are general).
    L=s.Symbol('L',positive=True); z=s.Symbol('z'); w2=1+z*z; w4=1+z**4
    oldphi=z*z+2*z-1; I2=s.integrate(w2,(z,0,L)); I4=s.integrate(w4,(z,0,L))
    C=-s.integrate(oldphi,(z,0,L))/(2*I2)
    xi=s.integrate(-2*C*w2-oldphi,z);xi=xi-xi.subs(z,0)
    assert s.factor(xi.subs(z,L))==0
    oldbeta=z**3-z; corrected=oldbeta+w2*xi
    H=s.integrate(corrected,(z,0,L))/I4
    U=s.integrate(H*w4-corrected,z);U=U-U.subs(z,0)
    assert s.factor(U.subs(z,L))==0
    assert s.factor(oldphi+xi.diff(z)+2*C*w2)==0
    assert s.factor(corrected+U.diff(z)-H*w4)==0
    print('PASS independent full Ricci mixed/normal/tangential trace identities')
    print('PASS Proca divergence, residual coordinate gauge, periodic normal holonomy BIDI')

if __name__=='__main__':run()
