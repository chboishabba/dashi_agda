"""One-way, dimensionless KK-inspired scalar exterior test using actual TDGL traces.
Standard Klein-Gordon lattice and positive quartic EFT; no claim of 5D stabilization.
Source profile and unit coupling are selected fixtures, not SI or a rotor geometry.
"""
import numpy as np
from scipy.integrate import solve_ivp
from check_sc_tdgl_maxwell_braking import model

def propagate(ts, invariant, mass, quartic, dx=.2, coupling=1., tol=1e-8):
    # Fixed end points, causal semidiscrete wave approximation, sponge at edges.
    x=np.arange(-32+dx,32,dx); n=len(x)
    profile=np.exp(-x*x/2); profile/=dx*profile.sum()
    damp=2*np.maximum((abs(x)-24)/8,0)**2
    source=invariant-invariant[0]
    def lap(q): return (np.r_[q[1:],0]-2*q+np.r_[0,q[:-1]])/dx**2
    def energy(q,v):
        return dx*(.5*np.sum(v*v+mass**2*q*q)+quartic/4*np.sum(q**4)+.5*np.sum(np.diff(np.r_[0,q,0])**2)/dx**2)
    def rhs(t,z):
        q,v=z[:n],z[n:2*n]; j=coupling*np.interp(t,ts,source)*profile
        return np.r_[v,lap(q)-mass**2*q-quartic*q**3-damp*v+j,dx*np.dot(j,v),dx*np.dot(damp,v*v)]
    sol=solve_ivp(rhs,(ts[0],ts[-1]),np.zeros(2*n+2),t_eval=ts,rtol=tol,atol=tol/100,max_step=.04)
    assert sol.success
    q,v=sol.y[:n],sol.y[n:2*n]; W,Q=sol.y[-2:]
    E=np.array([energy(a,b) for a,b in zip(q.T,v.T)])
    err=np.max(abs(E-W+Q)); assert err<2e-6
    # gradient proxy for conformal matter acceleration, NOT a calibrated force
    grad=(q[2:]-q[:-2])/(2*dx); probe=np.argmin(abs(x[1:-1]-5))
    return np.array([np.max(abs(q[probe+1])),np.max(abs(grad[probe])),W[-1],E[-1],err]),grad[probe]

def main():
    traces=model(capture=True)
    for mass,quartic in ((.2,0),(1.,0),(.2,10.)):
        waves={}
        for key,(ts,inv) in traces.items():
            v,w=propagate(ts,inv,mass,quartic); waves[key]=w
            print('scalar',mass,quartic,key,v)
        print('factorial gradient peak',np.max(abs(waves[1,1]-waves[1,0]-waves[0,1]+waves[0,0])))
    ts,inv=traces[1,1]
    a,w=propagate(ts,inv,.2,0); b,z=propagate(ts,inv,.2,0,dx=.1)
    print('mesh comparison',a,b,'relative gradient peak change',abs(b[1]/a[1]-1))
    assert abs(b[1]/a[1]-1)<.1
    c,u=propagate(ts,inv,.2,0,coupling=.5); assert np.max(abs(u-.5*w))<1e-6
    d,y=propagate(ts,inv,.2,0,coupling=0); assert np.max(abs(d))==0
    print('PASS scalar ledger, mesh comparison, linear source scaling, zero coupling')
if __name__=='__main__':main()
