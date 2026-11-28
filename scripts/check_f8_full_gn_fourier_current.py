"""F8 all-tangential-Fourier 5D Gaussian-normal scalar wave current.
One nonzero k vector is reduced by SO(3) invariance to its norm.
Exact signed wall energy, redshift deformation and mixed-jet off-shell audit.
Principal scalar components only: not coupled Einstein-Israel coercivity.
"""
import sympy as s

def exact():
    a,N,k=s.symbols('a N k',positive=True)
    p,q,u=s.symbols('p q u',real=True)
    at,an,Nt,Nn,pt,pn,qt,qn=s.symbols('at an Nt Nn pt pn qt qn',real=True)
    xs=(a,N,p,q,u)
    def deriv(expr,vals):return sum(s.diff(expr,x)*dx for x,dx in zip(xs,vals))
    dt=lambda x:deriv(x,(at,Nt,pt,qt,p))
    dn=lambda x:deriv(x,(an,Nn,pn,qn,q))
    kinetic=(p*p/N**2+q*q)/2
    tangential=k*k*u*u/(2*a*a)
    E=kinetic+tangential
    Jt=-a**3*E;Jn=a**3*p*q
    dens_wave=-dt(a**3*p/N)+dn(N*a**3*q)-N*a*k*k*u
    lhs=dt(Jt)+dn(Jn)-dens_wave*p/N
    deform=3*a*a*at*(p*p/N**2-q*q)/2-at*k*k*u*u/2-a**3*Nn*p*q/N
    assert s.factor((lhs-deform).subs(pn,qt))==0
    assert s.factor(lhs-deform-a**3*q*(pn-qt))==0
    # Exact |deformation| <= a³(3a_t/a + |N_n|) E
    # for a_t>=0; handle the F8 physical N_n negative explicitly.
    nu=s.symbols('nu',nonnegative=True)
    signed=deform.subs(Nn,-nu)
    coef=3*at/a+nu
    plus=a**3*coef*E+signed
    minus=a**3*coef*E-signed
    pp=a**3*(3*at/a*p*p/N**2+(2*at/a+nu)*tangential+nu/2*(p/N+q)**2)
    mm=a**3*(3*at/a*q*q+(4*at/a+nu)*tangential+nu/2*(p/N-q)**2)
    assert s.simplify(plus-pp)==0
    assert s.simplify(minus-mm)==0
    # F8 actual wall: a=t,N=1,a_t=1,N_n=-1/B.
    t=s.symbols('t',positive=True);B=s.sqrt(1+t**-2)
    wall={a:t,N:1,at:1,Nn:-1/B}
    expected=3*t*t*(p*p-q*q)/2-k*k*u*u/2+t**3*p*q/B
    assert s.simplify(deform.subs(wall)-expected)==0
    assert s.simplify(Jt.subs(wall)+t**3*(p*p+q*q+k*k*u*u/t**2)/2)==0
    assert s.simplify(Jn.subs(wall)-t**3*p*q)==0
    # Wall flux remains sign-indefinite even if the principal energy is positive.
    assert Jn.subs({a:1,p:1,q:1})>0 and Jn.subs({a:1,p:1,q:-1})<0
    # Gradient-free zero mode reduces to the earlier GN source current.
    assert s.simplify(deform.subs(k,0)-(3*a*a*at*(p*p/N**2-q*q)/2-a**3*Nn*p*q/N))==0
    print('PASS F8 exact 5D GN all-Fourier-principal current, two SOS bounds, signed wall and offshell mixed jet')
if __name__=='__main__':exact()
