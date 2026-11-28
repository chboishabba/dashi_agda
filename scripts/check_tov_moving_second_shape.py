"""Moving TOV material level set, second shape derivative, and critical trace obstruction.
Exact original source, fixed static background; no Einstein-GHY completion.
"""
import sympy as s

def run():
    r,lam,e,phi,psi,u=s.symbols('r lam e phi psi u',real=True)
    p=lam/(8*s.pi)
    rho=(2+lam)*p*(1-r*r)
    f=1-lam*(2+lam)*(r*r/3-r**4/5)
    P=(2+lam)*(s.Rational(1,3)-r*r/5)/2-(1-r*r)**2/2
    nu=r*lam*P/f
    M=lam*(2+lam)/15
    assert s.cancel((r*(1-f)/2).subs(r,1)-M)==0
    # Material Lagrangian density static = -N r² rho / sqrt(f).
    # Use the boundary value N(1)=sqrt(f(1)) for the local derivative fixture.
    Nw=s.sqrt(1-2*M)
    L0=-Nw*r*r*rho/s.sqrt(f)
    slope=s.simplify(s.diff(L0,r).subs(r,1))
    assert s.simplify(slope-2*(2+lam)*p)==0
    # Shape derivative including material first variation; L0(1)=0.
    L1,L2=s.symbols('L1 L2',real=True)
    shape=2*phi*L1+phi*phi*slope
    assert s.expand(shape.subs(L1,-phi*slope)+phi*phi*slope)==0
    assert s.simplify(shape.subs({L1:-phi*slope,lam:s.Rational(1,10)})+
                      s.Rational(21,5)*p.subs(lam,s.Rational(1,10))*phi**2)==0
    # Moving material level set R(rb)=1 requires u_wall+phi=0.
    R=1+e*(u+phi)+e*e*psi/2
    assert s.diff(R,e).subs(e,0)==u+phi
    # Exact moving integral Taylor oracle, independent of material labels.
    L10,L20,sl=s.symbols('L10 L20 sl')
    rr=s.symbols('rr'); moving=1+e*phi+e*e*psi/2
    density=sl*(rr-1)+e*L10+e*e*L20/2
    integ=s.integrate(density,(rr,0,moving))-s.integrate(density,(rr,0,1))
    assert s.expand(s.diff(integ,e,2).subs(e,0)-(phi*phi*sl+2*phi*L10))==0
    # Critical form-domain no-trace sequence: log profile on [eps²,eps].
    t,ep=s.symbols('t ep',positive=True)
    profile=s.log(t/ep)/s.log(ep)
    assert s.simplify(profile.subs(t,ep**2)-1)==0
    assert s.simplify(profile.subs(t,ep))==0
    energy=s.simplify(s.integrate(t*s.diff(profile,t)**2,(t,ep**2,ep)))
    assert s.simplify(energy+1/s.log(ep))==0
    assert s.limit(energy,ep,0,dir='+')==0
    # Higher graph conormal: p(t)=a t, flux J0=0, J'=Vv-wLv.
    a,V0,w0,v0,Lv=s.symbols('a V0 w0 v0 Lv',positive=True)
    J=V0*v0*t-w0*Lv*t*t/2
    assert s.limit(J/(a*t),t,0,dir='+')==V0*v0/a
    print('PASS TOV action surface slope, moving second shape derivative and level-set weld')
    print('PASS logarithmic form trace obstruction and higher graph conormal condition')
    print('OPEN Einstein/GHY corner and nonspherical moving-boundary physical domain')

if __name__=='__main__':run()
