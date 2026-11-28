"""W3.2 nonlinear radial Einstein constraint + original-action Euler acceleration.
Shoot original covariant scalar rho,p from a,d,V with Y=r+k*r(r²-1)/2,
Y_t=-r*(lam+2)/(lam+1+r²)*speed. Independently enforce exact wall
N²=f and scalar Euler trace. This is a finite radial initial-data
construction, NOT coupled time evolution, Israel GHY or continuum proof.
"""
import argparse
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp,simpson
from scipy.optimize import root


def coefficients(lam):
    x,l=s.symbols("x l",real=True)
    p=l/(8*s.pi);rho=(l+2)*p*(1-x);pr=-p*(1-x)**2
    F=1-l*(l+2)*(x/3-x*x/5)
    P=(l+2)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    pt=pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*F)
    a=(rho+pt)/2;d=(rho+pr)/(2*F);V=rho-2*a-d*F
    fn=s.lambdify((x,l),(a,d,V,s.diff(a,x),s.diff(d,x),s.diff(V,x)),
                  "numpy",cse=True)
    return lambda y:fn(y*y,lam)


def run(lam=.1,speed=.02,n=240):
    assert n>=80 and 0<lam<=.25 and abs(speed)<.15
    coeff=coefficients(lam);alpha=lam*(lam+2)
    f0wall=1-2*alpha/15
    r0=1.e-5
    def field(r,k):
        return (r+k*r*(r*r-1)/2,
                1+k*(3*r*r-1)/2,
                -r*(lam+2)/(lam+1+r*r)*speed)
    def solve_radial(k,Nc):
        def rhs(r,z):
            m,N=z
            F=1-2*m/r
            if N<=0 or F<=0:raise ValueError("timelike radial domain violated")
            Y,Yr,U=field(r,k);a,d,V,*_=coeff(Y)
            kin=d*(F*Yr*Yr+U*U/(N*N))
            angular=2*a*Y*Y/(r*r)
            rho=kin+angular+V;p=kin-angular-V
            return [4*np.pi*r*r*rho,N*(m+4*np.pi*r**3*p)/(r*r*F)]
        Y,Yr,_=field(r0,k);a,d,V,*_=coeff(Y)
        rhoc=(d+2*a)*Yr**2+V
        initial=(4*np.pi*rhoc*r0**3/3,Nc)
        sol=solve_ivp(rhs,(r0,1),initial,rtol=1e-9,atol=1e-11,
                      dense_output=True,max_step=1/n)
        if not sol.success:raise ValueError(sol.message)
        m,N=sol.y[:,-1];F=1-2*m
        # Exact source-matched Schwarzschild lapse and material Euler wall.
        return sol,m,N,F,F*(1+k)**2-speed**2/N**2-f0wall,N**2-F
    def residual(z):
        _,_,_,_,el,clock=solve_radial(*z)
        return [el,clock]
    guess=(speed**2/(2*f0wall**2),np.sqrt(f0wall)*.99)
    z=root(residual,guess,tol=1e-10)
    if not z.success:raise ValueError(z.message)
    k,Nc=z.x
    sol,m,N,F,wall_el,wall_clock=solve_radial(k,Nc)
    assert max(abs(wall_el),abs(wall_clock))<5e-10
    radii=np.linspace(r0,1,n+1);mm,nn=sol.sol(radii)
    Y,Yr,U=field(radii,k)
    a,d,V,ax,dx,Vx=coeff(Y)
    ff=1-2*mm/radii
    kin=d*(ff*Yr**2+U**2/nn**2)
    angular=2*a*Y**2/radii**2
    rho=kin+angular+V;p=kin-angular-V
    independent_mass=mm[0]+simpson(4*np.pi*radii**2*rho,x=radii)
    mass_err=independent_mass-m
    assert abs(mass_err)<1e-7 and min(ff)>0 and min(nn)>0
    assert abs(rho[-1])<1e-10 and abs(p[-1])<1e-10
    # Einstein spatial/time constraints give f_r,nu_r,f_t exactly on this
    # slice, with current from the SAME material action, not fitted j.
    fr=2*mm/radii**2-8*np.pi*radii*rho
    nu=(mm+4*np.pi*radii**3*p)/(radii**2*ff)
    j=-2*d*np.sqrt(ff)*U*Yr/nn
    ft=8*np.pi*radii*nn*np.sqrt(ff)*j
    Yrr=3*k*radii
    # Set N_t=0 as an explicitly conditional temporal gauge jet.
    # The actual Einstein lapse time evolution remains unpaid.
    spatial=(2*Y*dx*(-ff*Yr**2+U**2/nn**2)+4*Y*ax*Y**2/radii**2+
             4*a*Y/radii**2+2*Y*Vx-d*fr*Yr-2*d*ff*Yrr
             -2*d*ff*Yr*(2/radii+nu)-d*U*ft/(ff*nn**2))
    acceleration=np.full_like(spatial,np.nan)
    np.divide(-nn**2*spatial,2*d,out=acceleration,where=np.abs(d)>1e-14)
    assert abs(spatial[-1])<1e-12
    assert np.isfinite(acceleration[4:-4]).all()
    assert np.max(np.abs(acceleration[4:-4]))<.1
    print("W3.2",dict(lambda_=lam,speed=speed,n=n,k=float(k),
            ADM_mass=float(m),central_lapse=float(Nc),
            wall_Euler=float(wall_el),wall_lapse_match=float(wall_clock),
            mass_simpson_error=float(mass_err),
            acceleration_r50=float(acceleration[n//2]),
            acceleration_r90=float(acceleration[int(n*.9)]),
            acceleration_max_interior=float(np.max(np.abs(acceleration[4:-4])))),
          flush=True)
    return k,m


if __name__=="__main__":
    arg=argparse.ArgumentParser()
    arg.add_argument("--n",type=int,nargs="+",default=[120,240,480])
    arg.add_argument("--lam",type=float,default=.1)
    arg.add_argument("--speed",type=float,default=.02)
    cfg=arg.parse_args()
    data=[run(cfg.lam,cfg.speed,n) for n in cfg.n]
    if len(data)>1:assert abs(data[0][0]-data[-1][0])<5e-7
    # Signed flux reverses under velocity reversal, mass/gradient do not.
    if cfg.speed!=0 and cfg.n==[120,240,480]:
        forward=run(cfg.lam,-cfg.speed,240)
        assert np.allclose(data[1],forward,rtol=1e-7,atol=1e-10)
    print("PASS nonlinear original-action radial Einstein/wall and conditional Euler bulk initial jets")
    print("OPEN Nt Einstein gauge compatibility, full bulk evolution, angular Einstein, Israel/GHY")
