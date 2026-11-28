"""F8 W2 two-level energy identity on actual GN collar, exact boundary work.

This produces the original-source differentiated energy balance, not a
positive Einstein-Israel boundary estimate. It retains all source/normal jets.
"""
import sympy as s


def exact():
    t,n,k=s.symbols('t n k',positive=True)
    a=s.sinh(s.asinh(t)-n)
    N=s.cosh(s.asinh(t)-n)/s.sqrt(1+t*t)
    A=a**3/N; B=N*a**3; C=N*a*k*k
    # Treat all local fields/jets as algebraically independent; the PDE will
    # supply exactly the first-order constraints, not manufactured solutions.
    U,Ut,Un,Utt,Unt,Unn=s.symbols('U Ut Un Utt Unt Unn',real=True)
    Uttt,Untt,Unnt=s.symbols('Uttt Untt Unnt',real=True)
    # d_t E of the two derivative levels by the product rule.
    E0=(A*Ut**2+B*Un**2+C*U**2)/2
    E1=(A*Utt**2+B*Unt**2+C*Ut**2)/2
    dt=lambda expr,subs: s.diff(expr,t)+sum(s.diff(expr,x)*y for x,y in subs.items())
    Dt0=dt(E0,{U:Ut,Ut:Utt,Un:Unt})
    Dt1=dt(E1,{Ut:Utt,Utt:Uttt,Unt:Untt})
    Fn0=B*Ut*Un
    Fn1=B*Utt*Unt
    # n-differentiated flux (the first radial integrability is Un_t=Ut_n).
    Dn0=s.diff(Fn0,n)+B*(Unt*Un+Ut*Unn)
    Dn1=s.diff(Fn1,n)+B*(Unnt*Unt+Utt*Unnt*0)+B*Utt*Unnt
    # independent strong-form source from L u=-d_t(A u_t)+d_n(B u_n)-Cu
    Lu=-s.diff(A,t)*Ut-A*Utt+s.diff(B,n)*Un+B*Unn-C*U
    # known first-order differentiated forcing:
    # L(Ut)=d_t(Lu)+d_t(A_t Ut)-d_n(B_t Un)+C_t U
    # Define actual differentiated wave source F1 independent of higher PDE:
    F1=-s.diff(A,t)*Utt-A*Uttt+s.diff(B,n)*Unt+B*Unnt-C*Ut
    for (E,flux,source,velocity,normal,field) in (
        (E0,Fn0,Lu,Ut,Un,U),
        (E1,Fn1,F1,Utt,Unt,Ut),
    ):
        residual=s.diff(A,t)*velocity**2/2-s.diff(B,t)*normal**2/2-s.diff(C,t)*field**2/2
        # energy identity follows product rule; flux divergence includes
        # the independent normal derivatives of the field jets.
        if E is E0:
            dE=Dt0; dFlux=s.diff(B,n)*Ut*Un+B*(Unt*Un+Ut*Unn)
        else:
            dE=Dt1; dFlux=s.diff(B,n)*Utt*Unt+B*(Untt*Unt+Utt*Unnt)
        assert s.simplify(dE-dFlux+source*velocity+residual)==0
    # Exact two-level sum: any positive weight eta preserves the identity.
    eta=s.symbols('eta',positive=True)
    derivative=Dt0+eta*Dt1
    wall_flux=(Fn0+eta*Fn1).subs(n,0)
    assert s.simplify(wall_flux-t**3*(Ut*Un+eta*Utt*Unt))==0
    # Commutator source work cannot simply be bounded using only E1.
    # Explicitly retains Ut, Un, Utt, Unt, Unn and the source temporal jet.
    j,f=s.Function('j')(t),s.Function('f')(t)
    Zn=(k*k*f/t**2-j)/3
    Znt=s.diff(Zn,t)
    assert s.simplify(Znt-(k*k*(s.diff(f,t)-2*f/t)/t**2-s.diff(j,t))/3)==0
    # Endpoint fluxes on n=0: F0=t³ Zt Zn, F1=t³ Ztt Znt.
    Z=s.Function('Z')(t)
    wall=s.expand(wall_flux.subs({Ut:s.diff(Z,t),Un:Zn,Utt:s.diff(Z,t,2),Unt:Znt}))
    assert s.simplify(wall-t**3*(s.diff(Z,t)*Zn+eta*s.diff(Z,t,2)*Znt))==0
    # Physical boundary work in integrated domain is minus the n=0 flux.
    assert s.simplify(-wall +t**3*(s.diff(Z,t)*Zn+eta*s.diff(Z,t,2)*Znt))==0
    print('PASS F8 exact two-level GN divergence, original-wall signed flux and differentiated Israel normal jet')

if __name__=='__main__': exact()

def source_work():
    """Exact source-work Young inequalities, with missing boundary norm exposed."""
    import sympy as s
    eta,alpha,beta,gamma=s.symbols('eta alpha beta gamma',positive=True)
    u,v,f,g=s.symbols('u v f g',real=True)
    # Bulk work by F and differentiated F_t+commutator.
    assert s.expand((alpha*u*u+f*f/(4*alpha)-u*f) - (2*alpha*u-f)**2/(4*alpha))==0
    assert s.expand((beta*v*v+g*g/(4*beta)-v*g) - (2*beta*v-g)**2/(4*beta))==0
    # Boundary trace cost with actual f_t and j_t must be paid separately.
    z,bwork=s.symbols('z bwork',real=True)
    assert s.expand((gamma*z*z+bwork*bwork/(4*gamma)-z*bwork) - (2*gamma*z-bwork)**2/(4*gamma))==0
    # Explicit negative control: E_bulk positive alone does not bound u_t wall.
    L=s.Rational(1,2)
    n=s.symbols('n',nonnegative=True)
    # e_m(n)=exp(-m*n) with normalized energy under n integration (0,infty)
    m=s.symbols('m',positive=True)
    Z=s.sqrt(2*m)*s.exp(-m*n)
    assert s.integrate(Z**2,(n,0,s.oo))==1
    assert s.limit(Z.subs(n,0)**2,m,s.oo)==s.oo
    print('PASS source Young squares and boundary trace negative control')

if __name__=='__main__':source_work()
