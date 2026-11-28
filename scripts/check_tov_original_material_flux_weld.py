"""W2.4 original repaired TOV dynamical material radial momentum obstruction.
Derives stress from the SAME a,d,V source action, not a fitted j.
Shows uniform label scaling fails the W2.3 Einstein mass-flux interior at
first velocity order; reverse solves a smooth compatible material time jet.
No full nonlinear material equation, second metric jet or GHY claim.
"""
import sympy as s


def zero(z):
    assert s.simplify(s.factor(z))==0,s.factor(z)


def main():
    x,r,lam=s.symbols('x r lam',positive=True)
    pp=lam/(8*s.pi)
    rho0=(2+lam)*pp*(1-x)
    pr0=-pp*(1-x)**2
    f0=1-lam*(2+lam)*(x/3-x*x/5)
    P=(2+lam)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    pt0=pr0+x*s.diff(pr0,x)+x*lam*(rho0+pr0)*P/(2*f0)
    aa=(rho0+pt0)/2
    dd=(rho0+pr0)/(2*f0)
    VV=rho0-2*aa-dd*f0
    # Y^A=Y(t,r) n^A: same original K_AB=aI+bY_A Y_B, radial d=a+bY².
    Y,Yt,Yr=s.symbols('Y Y_t Y_r',real=True)
    N,f=s.symbols('N f',positive=True)
    aY=aa.subs(x,Y*Y);dY=dd.subs(x,Y*Y);vY=VV.subs(x,Y*Y)
    W=s.expand(dY*(f*Yr*Yr-Yt*Yt/(N*N))+2*aY*Y*Y/(r*r)+vY)
    # Original stress from L=-sqrt(-g) W; Eulerian density, radial stress
    # and signed radial flux follow from metric variation exactly.
    Ttt=s.expand(2*dY*Yt*Yt+N*N*W)
    Trr=s.expand(2*dY*Yr*Yr-W/f)
    Ttr=2*dY*Yt*Yr
    density=s.simplify(Ttt/(N*N))
    pressure=s.simplify(f*Trr)
    flux=-s.sqrt(f)*Ttr/N
    zero(density-W-2*dY*Yt*Yt/(N*N))
    zero(pressure-(2*dY*f*Yr*Yr-W))
    zero(flux+2*dY*s.sqrt(f)*Yt*Yr/N)
    orig={Y:r,Yt:0,Yr:1,f:f0.subs(x,r*r)}
    zero(density.subs(orig)-rho0.subs(x,r*r))
    zero(pressure.subs(orig)-pr0.subs(x,r*r))
    zero(flux.subs(orig))
    # Uniform material-label scaling Y=r/S(t) is what the W2.3
    # nonstationary mass profile implicitly suggests. At S=1, it has
    # Y_t=-r*Sdot, Y_r=1. Compare the *original* action current to the
    # W2.3 mass-derived current, keeping the SAME original f and rho.
    Sdot=s.symbols('Sdot',real=True)
    fm=f0.subs(x,r*r);rm=rho0.subs(x,r*r);pm=pr0.subs(x,r*r)
    trial_flux=s.simplify(flux.subs({Y:r,Yt:-r*Sdot,Yr:1,f:fm}))
    mass_flux=rm*r*Sdot/(N*s.sqrt(fm))
    zero(trial_flux-(rm+pm)*r*Sdot/(N*s.sqrt(fm)))
    residual=s.factor(trial_flux-mass_flux)
    zero(residual-pm*r*Sdot/(N*s.sqrt(fm)))
    assert residual!=0
    # It is zero at the original boundary because pressure vanishes there,
    # but NOT on the interior; surface matching alone is not bulk closure.
    zero(residual.subs(r,1))
    witness=s.factor(residual.subs({r:s.Rational(1,2),lam:s.Rational(1,10),Sdot:s.Rational(1,100),N:1}))
    assert witness!=0
    # Reverse-solve *at the original static slice* the material velocity
    # needed to match the Einstein mass flux, without changing source K.
    Yt_req=s.solve(s.Eq(flux.subs({Y:r,Yr:1,f:fm}),mass_flux),Yt)[0]
    expected=-rm*r*Sdot/(rm+pm)
    zero(Yt_req-expected)
    ratio=s.factor(rm/(rm+pm))
    zero(ratio-(lam+2)/(lam+1+r*r))
    zero((Yt_req+r*Sdot).subs(r,1))
    # The necessary nonuniform velocity is finite at r=0 and r=1,
    # but it must satisfy material Euler/constitutive PDE and evolving
    # spatial label gradients; those are NOT provided here.
    zero(s.limit(ratio,r,0)-(lam+2)/(lam+1))
    zero(s.limit(ratio,r,1)-1)
    # Turn off Sdot -> exact original static source; preserve causal sign.
    zero(residual.subs(Sdot,0))
    print('PASS original TOV material stress and radial flux from covariant action')
    print('PASS uniform-scaling nonzero interior obstruction; zero wall mismatch')
    print('PASS reverse-solved smooth material velocity and original wall kinematics')
    print('OPEN actual material Euler PDE, nonlinear metric, angular stress and GHY')


if __name__=='__main__':main()
