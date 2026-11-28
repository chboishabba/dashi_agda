"""W2.3 nonstationary spherical Einstein radial-constraint family.
Scale original TOV density/pressure shape by moving R(t), and derive
m, rho, p_r, f, lapse spatial slope and signed energy flux exactly.
This is a constructed Einstein radial source, NOT an original repaired
material-action solution or complete dynamical Einstein spacetime.
"""
import sympy as s


def zero(z):
    assert s.factor(s.cancel(z))==0,s.factor(z)


def main():
    r,R,lam=s.symbols('r R lam',positive=True)
    Rt,N=s.symbols('R_t N',real=True)
    alpha=lam*(lam+2)
    M=alpha/15
    p0=lam/(8*s.pi)
    x=r/R
    m=alpha*(x**3/s.Integer(3)-x**5/s.Integer(5))/2
    rho=alpha*(1-x*x)/(8*s.pi*R**3)
    pressure=-p0*(1-x*x)**2/R**3
    f=1-2*m/r
    nu=(m+4*s.pi*r**3*pressure)/(r*r*f)
    # Original Einstein constraint values, and nonzero mass transport.
    zero(s.diff(m,r)-4*s.pi*r*r*rho)
    zero(s.diff(m,R)*Rt+4*s.pi*r*r*N*s.sqrt(f)*rho*r*Rt/(R*N*s.sqrt(f)))
    j=rho*r*Rt/(R*N*s.sqrt(f))
    zero(s.diff(m,R)*Rt+4*s.pi*r*r*N*s.sqrt(f)*j)
    zero(s.diff(f,R)*Rt-8*s.pi*r*N*s.sqrt(f)*j)
    # The same m supplies both time and radial derivatives, hence the
    # integrability identity is not imposed on independent source fields.
    zero(s.diff(4*s.pi*r*r*rho,R)*Rt+s.diff(4*s.pi*r*r*N*s.sqrt(f)*j,r))
    # Original TOV at R=1, Rt=0: exact radial metric, pressure,
    # density, and lapse logarithmic slope from prior original action.
    f0=1-alpha*(r*r/3-r**4/5)
    rho0=alpha*(1-r*r)/(8*s.pi)
    pres0=-p0*(1-r*r)**2
    P=(lam+2)*(s.Rational(1,3)-r*r/5)/2-(1-r*r)**2/2
    nu0=r*lam*P/f0
    zero(f.subs(R,1)-f0)
    zero(rho.subs(R,1)-rho0)
    zero(pressure.subs(R,1)-pres0)
    zero(nu.subs(R,1)-nu0)
    # Every moving surface r=R has the same exterior Misner-Sharp mass,
    # zero stress/energy flux and matched f_r / N_r/N static spatial jets.
    zero(m.subs(r,R)-M)
    for z in (rho,pressure,j):zero(z.subs(r,R))
    F=1-2*M/r
    zero((f-F).subs(r,R))
    zero(s.diff(f-F,r).subs(r,R))
    zero((nu-M/(r*r*F)).subs(r,R))
    # Boundary N(R)=sqrt(1-2M/R) defines the lapse integration constant;
    # exp(integral nu dr) defines an exact positive radial lapse locally.
    # A physical moving solution requires its time derivatives and G_theta.
    wallrate=s.diff(m,R)*Rt+s.diff(m,r)*Rt
    zero(wallrate.subs(r,R))
    assert s.factor(s.diff(m,R))!=0 and s.factor(j)!=0
    print('PASS nonstationary original-profile Einstein radial mass+flux constraints')
    print('PASS exact original static TOV limit and moving vacuum wall traces')
    print('OPEN original constitutive stress, dynamic lapse/G_theta and evolution')

if __name__=='__main__':main()
