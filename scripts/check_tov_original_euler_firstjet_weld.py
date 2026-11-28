"""W2.5 original TOV action/Einstein first-time-jet compatibility.
Mass flux and density jet match; the prescribed scaled pressure fails.
The original pressure instead fixes a lapse-gradient correction.
No nonlinear Einstein/material evolution or boundary GHY proof.
"""
import sympy as s
def zero(x):
    z=s.factor(s.cancel(x))
    assert z==0,z
def main():
    r,lam,sd=s.symbols('r lam Sdot',positive=True)
    x=s.symbols('x',positive=True); p=lam/(8*s.pi)
    rho0=(lam+2)*p*(1-x); pr0=-p*(1-x)**2
    f0=1-lam*(lam+2)*(x/s.Integer(3)-x*x/s.Integer(5))
    P=(lam+2)*(s.Rational(1,3)-x/s.Integer(5))/2-(1-x)**2/2
    pt=pr0+x*s.diff(pr0,x)+x*lam*(rho0+pr0)*P/(2*f0)
    aa=(rho0+pt)/2; d=(rho0+pr0)/(2*f0)
    V=rho0-2*aa-d*f0
    Y,Yr,F=s.symbols('Y Yr F',real=True)
    aY=aa.subs(x,Y*Y);dY=d.subs(x,Y*Y);vY=V.subs(x,Y*Y)
    W=dY*F*Yr**2+2*aY*Y**2/r**2+vY
    density=W # at Y_t=0; time kinetic term is quadratic
    pressure=2*dY*F*Yr**2-W
    fb=s.factor(f0.subs(x,r*r))
    rb=s.factor(rho0.subs(x,r*r));pb=s.factor(pr0.subs(x,r*r))
    base={Y:r,Yr:1,F:fb}
    zero(density.subs(base)-rb);zero(pressure.subs(base)-pb)
    W_Y=s.diff(W,Y);W_Yr=s.diff(W,Yr)
    nu=r*lam*P.subs(x,r*r)/fb
    alpha=2/r+nu-s.diff(fb,r)/(2*fb)
    zero(W_Y.subs(base)-s.diff(W_Yr.subs(base),r)-alpha*W_Yr.subs(base))
    ft=lam*(lam+2)*r*r*(1-r*r)*sd
    rho_t_target=lam*(lam+2)/(8*s.pi)*(-3+5*r*r)*sd
    pressure_t_target=p*(1-r*r)*(3-7*r*r)*sd
    ratio=(lam+2)/(lam+1+r*r)
    yt=-r*ratio*sd;yrt=s.diff(yt,r)
    Ny=s.symbols('N',positive=True);yts=s.symbols('Y_t',real=True)
    flux=-2*dY*s.sqrt(F)*yts*Yr/Ny
    mass_flux=rb*r*sd/(Ny*s.sqrt(fb))
    zero(flux.subs(base).subs(yts,yt)-mass_flux)
    rho_t=s.factor(W_Y.subs(base)*yt+W_Yr.subs(base)*yrt+s.diff(W,F).subs(base)*ft)
    zero(rho_t-rho_t_target)
    pressure_t=s.factor(s.diff(pressure,Y).subs(base)*yt+
                      s.diff(pressure,Yr).subs(base)*yrt+s.diff(pressure,F).subs(base)*ft)
    gap=s.factor(pressure_t-pressure_t_target)
    assert gap!=0
    zero(gap.subs(r,1))
    witness=s.factor(gap.subs({r:s.Rational(1,2),lam:s.Rational(1,10),sd:1}))
    assert witness==s.Rational(77053,5043840)/s.pi
    # Einstein radial lapse constraint, with the SAME original stress,
    # requires a smooth spatial lapse time-jet adjustment.
    lapse_gradient_correction=s.factor(4*s.pi*r*gap/fb)
    zero(lapse_gradient_correction.subs(r,1))
    zero(s.limit(lapse_gradient_correction,r,0))
    # Derive both EL principal coefficients from the actual action,
    # rather than asserting a generic stability theorem.
    Ytime=s.symbols('Ytime',real=True)
    Wfull=W-dY*Ytime**2/Ny**2
    zero(s.diff(Wfull,Ytime,2).subs({Y:r,Yr:1,F:fb,Ytime:0})+2*d.subs(x,r*r)/Ny**2)
    zero(s.diff(Wfull,Yr,2).subs({Y:r,Yr:1,F:fb,Ytime:0})-2*d.subs(x,r*r)*fb)
    print('PASS original static material Euler and exact hyperbolic principal coefficients')
    print('PASS original material velocity matches Einstein mass flux AND density time jet')
    print('PASS nonzero scaled-pressure obstruction and regular Einstein lapse correction')
    print('PRESSURE_GAP_HALF=',witness)
    print('OPEN full Euler acceleration, angular Einstein equation, GHY and continuation')
if __name__=='__main__':main()
