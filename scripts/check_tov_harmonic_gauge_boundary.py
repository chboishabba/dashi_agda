#!/usr/bin/env python3
"""Exact 2+2 harmonic gauge transport, canonical junction jet and exterior energy.
Original radius-one TOV, lambda=1/10. No global constraint inversion or stability.
"""
import sympy as s


def gauge():
    t,r,th,ph=s.symbols('t r theta phi',real=True)
    x=(t,r,th,ph); N=s.Function('N')(r); f=s.Function('f')(r)
    g=s.diag(-N**2,1/f,r*r,r*r*s.sin(th)**2)
    Y=r*s.Matrix([s.sin(th)*s.cos(ph),s.sin(th)*s.sin(ph),s.cos(th)])
    T=1+t*r; R=r*r+t; z=t+r; eta=t*r+r*r
    q=g[:2,:2]; xi_cov=q*s.Matrix([T,R])
    clean=lambda M:M.applyfunc(lambda v:s.trigsimp(s.expand(v)))
    for ell in (1,2,3,4):
        L=ell*(ell+1); H=s.legendre(ell,s.cos(th)); dH=s.diff(H,th)
        tf=s.diff(H,th,2)+L*H/2
        Sphi=s.sin(th)*dH; Stp=(s.diff(Sphi,th)-2*s.cot(th)*Sphi)/2
        xi=s.Matrix([T*H,R*H,z*dH,eta*dH/s.sin(th)])
        Dx=xi.jacobian(x)
        lie=sum((xi[k]*g.diff(x[k]) for k in range(4)),s.zeros(4))+Dx.T*g+g*Dx
        pred=s.zeros(4)
        V=s.Matrix([T,R]); DV=V.jacobian((t,r))
        pred[:2,:2]=(T*q.diff(t)+R*q.diff(r)+DV.T*q+q*DV)*H
        for i in range(2):
            pred[i,2]=pred[2,i]=(xi_cov[i]+r*r*s.diff(z,x[i]))*dH
            pred[i,3]=pred[3,i]=r*r*s.diff(eta,x[i])*Sphi
        dk=2*R/r-L*z
        pred[2,2]=r*r*(dk*H+2*z*tf)
        pred[3,3]=r*r*s.sin(th)**2*(dk*H-2*z*tf)
        pred[2,3]=pred[3,2]=2*r*r*eta*Stp
        assert clean(lie-pred)==s.zeros(4),ell
        assert clean(Y.jacobian(x)*xi-(R*H*Y/r+z*dH*Y.diff(th)+eta*dH/s.sin(th)*Y.diff(ph)))==s.zeros(3,1)
        if ell==1:
            assert s.trigsimp(tf)==0 and s.trigsimp(Stp)==0
        else:
            assert tf!=0 and Stp!=0
        print('PASS exact Lie transport and tensor harmonic rank',ell,flush=True)
    # Generic amplitude gauge invariants for ell>=2.
    L=s.symbols('L',positive=True); j=s.Matrix(s.symbols('j0:2')); X=s.Matrix(s.symbols('X0:2'))
    dz=s.Matrix(s.symbols('dz0:2')); G,K,u,v,w,z,eta,b2,R=s.symbols('G K u v w z eta b2 R')
    dG=s.Matrix(s.symbols('dG0:2')); b=s.Matrix(s.symbols('b0:2')); db2=s.Matrix(s.symbols('db2_0:2')); de=s.Matrix(s.symbols('de0:2'))
    p=j-r*r*dG/2; pp=j+X+r*r*dz-r*r*(dG+2*dz)/2
    assert s.simplify(pp-p-X)==s.zeros(2,1)
    # X_r=R/f, hence r^a X_a=R. Even metric and displacement invariants.
    assert s.expand((K+2*R/r-L*z)+L*(G+2*z)/2-2*R/r-(K+L*G/2))==0
    assert s.expand(u+R-R-u)==0 and s.expand(v+r*z-r*(G+2*z)/2-(v-r*G/2))==0
    assert s.simplify(b+de-(db2+2*de)/2-(b-db2/2))==s.zeros(2,1)
    assert s.expand(w+r*eta-r*(b2+2*eta)/2-(w-r*b2/2))==0
    print('PASS even/odd gauge compensator algebra; l=1 tensor degeneracy retained')


def junction():
    e=s.symbols('e',real=True)
    gamma=s.diag(-2,3,5); K=s.Matrix([[1,2,0],[2,3,1],[0,1,4]])/7
    H=s.Matrix([[1,2,3],[2,-1,2],[3,2,4]])/11
    Q=s.Matrix([[2,-1,1],[-1,3,2],[1,2,-2]])/13
    A=gamma.inv(); dA=-A*H*A; tau=s.trace(A*K)
    dtau=s.trace(dA*K+A*Q); j=s.trace(A*H)/2
    pi=A*K*A-tau*A
    dpi=j*pi+dA*K*A+A*Q*A+A*K*dA-dtau*A-tau*dA
    gam=gamma+e*H; k=K+e*Q; inv=gam.inv()
    exact=s.sqrt(gam.det()/gamma.det())*(inv*k*inv-s.trace(inv*k)*inv)
    assert (exact.diff(e).subs(e,0)-dpi).applyfunc(s.simplify)==s.zeros(3)
    # Common induced metric variation; oriented momentum jump linear in K jet.
    Q2=Q+s.diag(1,0,0)/17
    d2=j*pi+dA*K*A+A*Q2*A+A*K*dA-s.trace(dA*K+A*Q2)*A-tau*dA
    assert (d2-dpi-(A*(Q2-Q)*A-s.trace(A*(Q2-Q))*A)).applyfunc(s.simplify)==s.zeros(3)
    assert d2!=dpi
    # Trace reversal in 3 boundary dimensions is injective.
    L=s.Matrix(3,3,lambda i,j:s.Symbol('L%d%d'%(min(i,j),max(i,j))))
    R=A*L*A-s.trace(A*L)*A
    assert (gamma*R*gamma-s.trace(gamma*R)*gamma/2-L).applyfunc(s.expand)==s.zeros(3)
    # Original TOV: matched Gaussian induced metric, K, and normal K jets
    # follow from f,f',nu',nu'' matching at r=1.
    r,l=s.symbols('r l',positive=True); f=1-l*(2+l)*(r*r/3-r**4/5)
    M=l*(2+l)/15; F=1-2*M/r
    P=(2+l)*(s.Rational(1,3)-r*r/5)/2-(1-r*r)**2/2
    nu=r*l*P/f; nv=M/(r*r*F)
    for z in (f-F,s.diff(f-F,r),nu-nv,s.diff(nu-nv,r)):
        assert s.cancel(z.subs(r,1))==0
    # Scalar normal derivative of mixed K eigenvalues sqrt(f)*nu', sqrt(f)/r.
    for a,b in ((nu,nv),(1/r,1/r)):
        assert s.cancel((f*s.diff(a,r)+s.diff(f,r)*a/2-F*s.diff(b,r)-s.diff(F,r)*b/2).subs(r,1))==0
    print('PASS canonical momentum jet, two-face jump negative control, trace reversal and TOV normal jets')


def exterior():
    r,M,n=s.symbols('r M n',positive=True); F=1-2*M/r; L=2*(n+1)
    RW=F*(L/r**2-6*M/r**3)
    Z=2*F*(n*n*(n+1)*r**3+3*n*n*M*r*r+9*n*M*M*r+9*M**3)/(r**3*(n*r+3*M)**2)
    y,k=s.symbols('y k',positive=True)
    # r=2M+y, n=2+k covers all ell>=2 including ell=2 by continuity.
    assert s.factor(RW.subs({r:2*M+y,n:2+k})).is_positive
    assert s.factor(Z.subs({r:2*M+y,n:2+k})).is_positive
    assert s.factor(RW.subs({r:2*M+y,n:2})).is_positive
    assert s.factor(Z.subs({r:2*M+y,n:2})).is_positive
    assert 1>2*s.Rational(1,10)*s.Rational(21,10)/15
    t,x=s.symbols('t x',real=True); psi=s.Function('psi')(t,x); V=s.Function('V')(x)
    E=(psi.diff(t)**2+psi.diff(x)**2+V*psi**2)/2
    flux=psi.diff(t)*psi.diff(x)
    assert s.expand(E.diff(t)-flux.diff(x)-psi.diff(t)*(psi.diff(t,2)-psi.diff(x,2)+V*psi))==0
    print('PASS all-mode positive Schwarzschild RW/Zerilli exterior potentials and energy current')


if __name__=='__main__':
    gauge();junction();exterior()
    print('OPEN actual harmonic constraint inverse, full moving GHY/corner Hessian, master-field reconstruction and interior-exterior flux estimate')
