"""Relative-strain causal tube and higher graph-domain boundary identities.
Pointwise matter principal symbol, not global Einstein free-boundary existence.
"""
import sympy as s


def main():
    n=s.Matrix(s.symbols('n:3',real=True)); b=s.Matrix(s.symbols('b:3',real=True))
    D=n*b.T+b*n.T
    assert s.expand(s.trace(D)**2-s.trace(D*D)-2*(n.dot(b)**2-n.dot(n)*b.dot(b)))==0
    # Normalized K_eff=K0+c(tr C I-C). In dimension 3,
    # ||tr C I-C|| <=2||C|| for real symmetric C.
    e=s.Rational(1,200); v=s.Rational(1,10); lam=s.Rational(1,10)
    slack=1-s.Rational(21,20)*s.Rational(50,93)
    # ||spatial normalized gradient||² <=1+e+v².
    # K0/c >=1+lam*slack; subtract 2e and spatial acoustic term.
    margin=lam*slack-3*e-v*v
    assert margin==s.Rational(23,1240) and margin>0
    print('PASS relative-strain causal tube margin',margin)
    # Exact moving-wall mixed extrinsic curvature for spherical polar-areal
    # metric ds²=-N²dt²+dr²/f+r²dOmega², outward normal.
    # For first order proper-time wall velocity and acceleration, velocity
    # products with metric time derivatives are second order.
    r,f,N,nu,df,dnu,phi,acc,fp,nup=s.symbols('r f N nu df dnu phi acc fp nup',real=True)
    eps=s.symbols('eps',real=True)
    F=f+eps*(df+phi*fp)
    Ktheta=s.sqrt(F)/(r+eps*phi)
    Ktau=s.sqrt(F)*(nu+eps*(dnu+phi*nup))+eps*acc/s.sqrt(F)
    kt=s.diff(Ktheta,eps).subs(eps,0)
    kk=s.diff(Ktau,eps).subs(eps,0)
    assert s.simplify(kt-(df+phi*fp)/(2*r*s.sqrt(f))+s.sqrt(f)*phi/r**2)==0
    assert s.simplify(kk-(df+phi*fp)*nu/(2*s.sqrt(f))-s.sqrt(f)*(dnu+phi*nup)-acc/s.sqrt(f))==0
    # Matched background f,f',nu',nu''; same wall acceleration;
    # delta f and delta nu' zero on each face => zero jump.
    # Independently compare faces with arbitrary perturbations:
    df2,dnu2=s.symbols('df2 dnu2',real=True)
    assert s.simplify(kk-kk.subs({df:df2,dnu:dnu2})-(df-df2)*nu/(2*s.sqrt(f))-s.sqrt(f)*(dnu-dnu2))==0
    assert s.simplify(kt-kt.subs(df,df2)-(df-df2)/(2*r*s.sqrt(f)))==0
    # Independent normal acceleration calculation with local metric jets.
    N,f=s.symbols('N f',positive=True)
    Nr,fr,Nt,ft,dN,df,dNr,vel,acc=s.symbols('Nr fr Nt ft dN df dNr vel acc',real=True)
    Nw=N+eps*dN; fw=f+eps*df; Nrw=Nr+eps*dNr
    rd=eps*vel; rdd=eps*acc
    Ud=s.sqrt(1+rd**2/fw)/Nw
    nr=s.sqrt(1+rd**2/fw)/s.sqrt(fw)
    ar=rdd+fw*Nw*Nrw*Ud**2-eps*ft/fw*Ud*rd-fr/(2*fw)*rd**2
    # n_t a^t is second order around a static wall in this chart.
    actual=s.diff(nr*ar,eps).subs(eps,0)
    expected=acc/s.sqrt(f)+df*Nr/(2*N*s.sqrt(f))+s.sqrt(f)*(dNr/N-Nr*dN/N**2)
    assert s.simplify(actual-expected)==0
    print('PASS spherical time-dependent linear Israel jump and independent normal acceleration')
    # Graph domain flux integral: for Lv continuous at endpoint, w~t,
    # V(t)v(t) continuous and p/t->a>0. J(0)=0 implies
    # v_t(0)=V(0)v(0)/a. Check leading model with a nonzero forcing.
    t,a,V0,v0,L0,w0=s.symbols('t a V0 v0 L0 w0',positive=True)
    J=s.integrate(V0*v0-w0*t*L0,t)
    assert s.limit(J/(a*t),t,0,dir='+')==V0*v0/a
    print('PASS higher graph-domain leading conormal identity')
    print('OPEN nonlinear coupled evolution and nonspherical physical boundary')


if __name__=='__main__':
    main()
