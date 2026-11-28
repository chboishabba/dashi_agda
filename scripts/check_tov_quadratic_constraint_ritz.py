"""W3 quadratic original-action spherical mass constraint and Euler wall trace.
Finite radial quadrature supplies candidate O(v²) data, not nonlinear Einstein
Euler evolution, angular constraint, or an existence theorem.
"""
import argparse
import numpy as np
import sympy as s
from scipy.integrate import cumulative_trapezoid

def run(n,lam=0.1,wall_speed=0.02):
    x,l=s.symbols("x l",real=True)
    p=l/(8*s.pi);rho=(l+2)*p*(1-x);pr=-p*(1-x)**2
    f=1-l*(l+2)*(x/3-x*x/5)
    P=(l+2)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
    pt=pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*f)
    a=(rho+pt)/2;d=(rho+pr)/(2*f);V=rho-2*a-d*f
    # H=k*r*(r²-1)/2, so H(1)=0 and H'(1)=k.
    # A is the action's exact first derivative of material rho in k.
    A=(x-1)*(x*(s.diff(d,x)*f+2*s.diff(a,x)+s.diff(V,x))+2*a)+d*f*(3*x-1)
    # Independently differentiate the ORIGINAL covariant material action,
    # rather than trusting the finite-volume source A as a fitted profile.
    y,yr,fr,rr=s.symbols("y yr fr rr",positive=True)
    W=d.subs(x,y*y)*fr*yr**2+2*a.subs(x,y*y)*y*y/rr**2+V.subs(x,y*y)
    drho=s.diff(W,y).subs({y:rr,yr:1,fr:f.subs(x,rr*rr)})*(rr*(rr*rr-1)/2)
    drho+=s.diff(W,yr).subs({y:rr,yr:1,fr:f.subs(x,rr*rr)})*((3*rr*rr-1)/2)
    assert s.cancel(drho-A.subs(x,rr*rr))==0
    ffun=s.lambdify((x,l),f,"numpy")
    dfun=s.lambdify((x,l),d,"numpy")
    Afun=s.lambdify((x,l),A,"numpy")
    nufun=s.lambdify((x,l),s.sqrt(x)*l*P/f,"numpy")
    r=np.linspace(0,1,n+1);xx=r*r
    f0=ffun(xx,lam);ds=dfun(xx,lam);aa=Afun(xx,lam)
    nu=nufun(xx,lam)
    integral=cumulative_trapezoid(nu,r,initial=0)
    N=np.sqrt(f0[-1])*np.exp(integral-integral[-1])
    U=-r*(lam+2)/(lam+1+r*r)*wall_speed
    B=ds*U*U/(N*N)
    alpha=8*np.pi*r*ds
    weight=np.exp(cumulative_trapezoid(alpha,r,initial=0))
    mass0=cumulative_trapezoid(weight*4*np.pi*r*r*B,r,initial=0)/weight
    mass1=cumulative_trapezoid(weight*4*np.pi*r*r*aa,r,initial=0)/weight
    denom=f0[-1]-mass1[-1]
    assert abs(denom)>1e-3 and np.all(f0>0)
    k=(mass0[-1]+U[-1]**2/(2*N[-1]**2))/denom
    mass=mass0+k*mass1
    delta_rho=k*aa+B-2*ds*mass/np.where(r>0,r,1)
    delta_rho[0]=k*aa[0]+B[0]
    rhs=4*np.pi*r*r*delta_rho
    mprime=np.gradient(mass,r,edge_order=2)
    err=np.max(abs(mprime[2:-2]-rhs[2:-2]))
    walltrace=2*f0[-1]*k-2*mass[-1]-U[-1]**2/N[-1]**2
    assert abs(walltrace)<1e-12
    assert abs(mass[0])<1e-14
    assert abs(delta_rho[-1])<1e-10
    assert err<3e-7
    print(f"n={n} k={k:.12g} m2wall={mass[-1]:.12g} fwall={f0[-1]:.12g} massode_residual={err:.2e} walltrace={walltrace:.2e}")
    return k,mass[-1],err

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--n",type=int,nargs="+",default=[256,512,1024])
    parser.add_argument("--lam",type=float,default=.1)
    parser.add_argument("--speed",type=float,default=.02)
    z=parser.parse_args()
    data=[run(n,z.lam,z.speed) for n in z.n]
    if len(data)>1:print("refinement spread k",abs(data[0][0]-data[-1][0]))
    print("PASS quadratic original-action Einstein radial mass/wall Euler compatibility candidate")
    print("OPEN momentum time constraint, angular Einstein, bulk Euler, exact moving embedding/GHY")
