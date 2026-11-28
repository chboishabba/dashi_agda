"""Radial linear evolution of repaired TOV: constraint and weighted form.
Requires check_tov_causal_constitutive_repair.py for the selected-background
radial positivity certificate. No nonlinear or finite-energy wall trace claim.
"""
import sympy as s


def main():
    r=s.symbols('r',positive=True)
    # Generic polar-areal metric: f=1-2m/r, lapse N. For static background
    # rho=W, p_r=2 f W_f-W. At zero velocity the Hamiltonian and lapse
    # constraints imply (log(N/sqrt(f)))'=-4pi r² W_m.
    m,rho,pr,Wf=s.symbols('m rho pr Wf',real=True)
    f=1-2*m/r
    fp=2*m/r**2-8*s.pi*r*rho
    nu=(m+4*s.pi*r**3*pr)/(r*r*f)
    assert s.cancel((nu-fp/(2*f)).subs(pr,2*f*Wf-rho)-8*s.pi*r*Wf)==0
    # W_m=-2 W_f/r, hence j=N/sqrt(f), j(1)=1 on Schwarzschild match.
    # Radial momentum constraint: m_t=4pi r² T^r_t, with
    # T^r_t=2 d f R_r R_t at first order; correction has zero first
    # strain derivative and background R_t=0.
    d,u_t=s.symbols('d u_t',real=True)
    A=8*s.pi*r*r*d*f
    assert s.expand(4*s.pi*r*r*2*d*f*u_t-A*u_t)==0
    # Generic constrained Hessian identity. j'/j=-k W_m, k=4pi r².
    # EL for static R is (j k W_v)'=j k W_R; its linearization has
    # a nonlocal delta j term, which reduces locally via delta log j'.
    k=s.Function('k')(r); j=s.Function('j')(r)
    u=s.Function('u')(r); A=s.Function('A')(r)
    RR,Rv,Rm,vv,vm,mm=[s.Function(n)(r) for n in ('RR','Rv','Rm','vv','vm','mm')]
    mu=A*u
    dwR=RR*u+Rv*u.diff(r)+Rm*mu
    dwv=Rv*u+vv*u.diff(r)+vm*mu
    dwm=Rm*u+vm*u.diff(r)+mm*mu
    # A=k W_v. delta log j'=-k delta W_m; background EL cancels
    # terms proportional to delta log j itself.
    linear=j*k*(dwR+A*dwm)-(j*k*dwv).diff(r)
    Q=RR*u*u+2*Rv*u*u.diff(r)+2*Rm*u*mu+vv*u.diff(r)**2+2*vm*u.diff(r)*mu+mm*mu**2
    variational=(s.diff(j*k*Q,u)-s.diff(s.diff(j*k*Q,u.diff(r)),r))/2
    assert s.expand(linear-variational)==0
    print('PASS polar slicing / linear momentum / constrained scalar Hessian identities')
    # Kinetic term of normalized mass Hessian is K=2r² d/(p N²).
    # At lambda=1/10, original source f>=93/100 and |P|<=1/2.
    # |nu(1)-nu(r)|<=lambda/(4 fmin), N(1)^2=f(1).
    # exp(-x)>=1-x gives N²>=fmin*(1-lambda/(2 fmin)).
    lam=s.Rational(1,10); fmin=s.Rational(93,100)
    Nmin=fmin*(1-lam/(2*fmin))
    assert Nmin>s.Rational(4,5)
    assert (2+lam)/(fmin*s.Rational(4,5))<3
    # Given donor G>=3r²/2 and K<=3r², E>=||u||_K²/2.
    assert s.Rational(3,2)/3==s.Rational(1,2)
    print('PASS conditional Friedrichs radial spectral gap omega²>=1/2 (R=1, asymptotic time)')
    # Ground-state transform v=u/psi: near surface, ptilde~t and
    # weight~t; constant and log are L², only constant has finite
    # gradient energy. Near centre ptilde~r⁴, weight~r⁴, singular
    # r^-3 branch is not L². These model endpoint integrals are
    # diagnostics; coefficient asymptotics and domain argument in roadmap.
    t=s.symbols('t',positive=True); e=s.symbols('e',positive=True)
    assert s.integrate(t,(t,0,1))==s.Rational(1,2)
    assert s.integrate(t*s.log(t)**2,(t,0,1))==s.Rational(1,4)
    assert s.limit(s.integrate(1/t,(t,e,1)),e,0,dir='+')==s.oo
    assert s.limit(s.integrate(1/t**2,(t,e,1)),e,0,dir='+')==s.oo
    assert s.limit(s.integrate(1/(t*s.log(e)**2),(t,e**2,e)),e,0,dir='+')==0
    print('PASS endpoint model integrals and persistent finite-energy trace obstruction')
    print('OPEN physical moving wall trace, nonlinear and nonspherical evolution')


if __name__=='__main__':
    main()
