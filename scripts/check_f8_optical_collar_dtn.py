"""Numerical finite collar DtN diagnostic on actual frozen F8 optical metric.
Not interval arithmetic, no full exterior matching or nonlinear propagation.
"""
import numpy as np
from scipy.integrate import solve_bvp, simpson
from scipy.optimize import brentq


def dtn(t,k,w,delta=1/8,tol=2e-8):
    beta=np.sqrt(1+t**-2)
    def geometry(n):
        A=np.cosh(n)-beta*np.sinh(n); N=np.cosh(n)-np.sinh(n)/beta
        return A,N
    def ode(n,y):
        A,N=geometry(n); V=k*k*((N/A)**2-1); u=y[0]+1j*y[1]; v=y[2]+1j*y[3]
        a=v/N; b=(w+V)*u/N
        return np.array([a.real,a.imag,b.real,b.imag])
    def bc(l,r):return np.array([l[0]-1,l[1],r[0],r[1]])
    n=np.linspace(0,delta,200); g=np.zeros((4,n.size));g[0]=1-n/delta;g[2]=-1/delta
    sol=solve_bvp(ode,bc,n,g,tol=tol,max_nodes=30000)
    if not sol.success:raise RuntimeError(sol.message)
    m=-complex(sol.y[2,0],sol.y[3,0])
    n=np.linspace(0,delta,16001); A,N=geometry(n); y=sol.sol(n);u=y[0]+1j*y[1];v=y[2]+1j*y[3]
    mass=simpson(abs(u)**2/N,x=n)
    work=simpson((abs(v)**2+(k*k*((N/A)**2-1)+w)*abs(u)**2)/N,x=n)
    assert abs(m-work)<3e-6*max(1,abs(m))
    return m,mass


def run():
    for t in (1.,3.,12.):
        beta=np.sqrt(1+t**-2); K=t**-2/(3*beta)-t**-4/12
        for k in (0.,100.,1000.):
            scale=max(1.,k**(4/3));w=scale*(1+1j)
            m,mass=dtn(t,k,w)
            assert abs(m.imag-w.imag*mass)<3e-6*max(1,abs(m))
            assert m.imag>0 and m.real>0
            if k:
                flat=brentq(lambda x:x*(np.sqrt(x)+8*K)-2*K*k*k,1e-12,k*k)
                R=brentq(lambda x:x*(dtn(t,k,x)[0].real+8*K)-2*K*k*k,1e-12,flat,xtol=1e-8)
                assert 0<R<flat
                print('t,k',t,k,'actual collar root / flat',R/flat)
    print('9 complex Green work controls and 6 actual finite collar surface roots PASS')


if __name__=='__main__':run()
