"""Conditional reciprocal periodic shell/spatial solve.
Uses existing frozen material/curl generator and layered shell radial propagator.
The harmonic truncation is a periodic Galerkin solve, not a causal initial-value
solver. DC and Nyquist are explicit separate real matched terminations.
All coordinates are normalized; no calibrated source or heater is asserted.
"""
import json
import numpy as np
from scipy.optimize import minimize
from solar_periodic_spatial import thermal
from solar_earth_spatial_transport import Grid, cell
from solar_periodic_radial_weld import layer, R, H

def shell_port(f, yg=1., sigma=1e-9):
    """Top driving-point admittance and ground transfer, same power units."""
    if f==0: return np.ones(6),np.zeros(6)
    if f<0:
        y,g=shell_port(-f,yg,sigma); return y.conj(),g.conj()
    ys=[]; gs=[]
    for typ in ('TE','TM'):
        M=np.eye(2,dtype=complex)
        for lo,hi,sg in ((R,R+H/2,0.),(R+H/2,R+H,sigma)):
            M=layer(f,lo,hi,sg,typ).y[:,-1].reshape(2,2)@M
        a,b=M@np.array([1.,-yg])
        y=-b/a; g=np.sqrt(yg)/a
        assert y.real>=abs(g)**2-1e-8*max(1.,abs(y))
        ys.extend([y]*3); gs.extend([g]*3)
    return np.array(ys),np.array(gs)

def geometry(n,ratio):
    """Two equal norm aperture channels, aspect ratio proxy, not antenna CAD."""
    x=(np.arange(n)+.5)/n-.5
    a=np.exp(-8*(x/ratio)**2); b=np.exp(-8*(x*ratio)**2)
    a/=np.linalg.norm(a); b/=np.linalg.norm(b)
    return np.column_stack((a,b))

def complement(x,restrict,lift):
    c=restrict@x; d=x-lift@c
    assert np.allclose(restrict@lift,np.eye(len(c)))
    assert np.allclose(restrict@d,0) and np.allclose(lift@c+d,x)
    return c,d

def solve(k,l,p,source,aperture,ports):
    n,N=2**k,2**l; dx=1/n; h=1/N
    p=np.asarray(p,float).reshape(N,n); assert np.all(p>=0)
    th,mid,cool=thermal(p,h)
    # Existing spatial dense generator, not a replacement Maxwell model.
    grids=[Grid(dx,[cell(1.,(1.,),(.5+v,),(-2.,),.3) for v in row],1.) for row in mid]
    A=np.array([g.dense()[0] for g in grids]); d=A.shape[1]
    C=np.zeros((6,d)); C[3,[6*i for i in range(n)]]=aperture[:,0]
    C[4,[6*i+1 for i in range(n)]]=aperture[:,1]
    # Power conjugate coupling: sheet voltage Cx, reaction -C^T Y Cx.
    # Unit-normalized DFT, spectral skew derivative. Real Nyquist derivative zero.
    freqs=np.fft.fftfreq(N,d=h); w=2*np.pi*freqs; w[N//2]=0
    F=np.fft.fft(np.eye(N),axis=0)/np.sqrt(N)
    deriv=(F.conj().T@(1j*w[:,None]*F)).real
    Y=np.array([ports[i][0] for i in range(N)]); G=np.array([ports[i][1] for i in range(N)])
    B=np.kron(deriv,np.eye(d))
    for i in range(N): B[i*d:(i+1)*d,i*d:(i+1)*d]-=A[i]
    # Construct real convolution matrix on original time coordinates.
    for q in range(6):
        K=(F.conj().T@(Y[:,q,None]*F)).real
        B+=np.kron(K,np.outer(C[q],C[q]))
    # Independent natural incident wave on first electric cell, matched port.
    c=np.zeros(d); c[0]=1.; B+=np.kron(np.eye(N),np.outer(c,c))
    inc=np.asarray(source,float); rhs=2*inc[:,None]*c
    x=np.linalg.solve(B,rhs.ravel()).reshape(N,d)
    field=x@c; outgoing=field-inc
    sh=F@(x@C.T); shwork=h*np.sum(Y.real*abs(sh)**2)
    ground=h*np.sum(abs(G*sh)**2)
    # local material and load dissipation from symmetric generator.
    loss=-h*np.einsum('ti,tij,tj->',x,A,x)
    load=h*.3*np.sum(x[:,:6*n].reshape(N,n,6)[...,:3]**2)
    paid=dx*h*p.sum(); incoming=h*(inc@inc); out=h*(outgoing@outgoing)
    err=incoming-out-loss-shwork
    assert abs(err)<1e-9*max(1.,incoming) and shwork>=ground-1e-9
    assert abs(paid-dx*cool)<1e-10
    if not np.any(inc): assert np.linalg.norm(x)<1e-12
    return dict(net=float(load+ground-paid),ground=float(ground),load=float(load),paid=float(paid),incident=float(incoming),outgoing=float(out),collision=float(loss-load),shell_other=float(shwork-ground),balance=float(err),history=x,thermal=th,dc=sh[0].real,nyquist=sh[N//2].real)

def fixtures():
    rows=[]
    for k,l in ((1,3),(2,3)):
        n,N=2**k,2**l; t=np.arange(N)/N; source=.4+.2*np.cos(2*np.pi*t)
        ports=[]
        for i in range(N):
            m=i if i<N//2 else i-N
            # Static DC and unresolved Nyquist are matched sinks, not radial solves.
            ports.append(shell_port(7.83*m) if i!=N//2 else shell_port(0))
        ratios={'square':1.,'3:2':1.5,'golden':(1+np.sqrt(5))/2}
        for name,r in ratios.items():
            C=geometry(n,r); zero=np.zeros((N,n))
            passive=solve(k,l,zero,source,C,ports)
            # Optimize only nonnegative heating amplitude of declared waveform.
            shape=np.broadcast_to(1+np.cos(2*np.pi*t[:,None]),(N,n))
            def objective(a): return -solve(k,l,a[0]*shape,source,C,ports)['net']
            opt=minimize(objective,[.01],bounds=[(0,.1)],method='L-BFGS-B')
            assert opt.success
            active=solve(k,l,opt.x[0]*shape,source,C,ports)
            off=solve(k,l,opt.x[0]*shape,source*0,C,ports)
            rows.append(dict(k=k,l=l,geometry=name,amplitude=float(opt.x[0]),passive=passive['net'],active=active['net'],source_off=off['net'],max_balance=max(abs(v['balance']) for v in (passive,active,off))))
        # Unrestricted over these two normalized real aperture vectors; local
        # optimization is a feasible lower bound, NOT a global upper bound.
        def unpack(v):
            v=v.reshape(n,2); return v/np.linalg.norm(v,axis=0)
        def obj(v): return -solve(k,l,np.zeros((N,n)),source,unpack(v),ports)['net']
        v=geometry(n,1.5).ravel(); best=minimize(obj,v,method='BFGS')
        rows.append(dict(k=k,l=l,geometry='unrestricted_passive_local',net=float(-best.fun),optimizer_success=bool(best.success)))
    return dict(status='CONDITIONAL_RECIPROCAL_PERIODIC_GALERKIN',rows=rows,physical_admission=False,scope='Synthetic normalized fixed population, reciprocal power-conjugate shell load; periodic spectral discretization, not causal initial value; DC/Nyquist matched sinks, not physical static radial; aspect ratio proxy; local aperture and scalar heating optimization, not global optimum.')
if __name__=='__main__': print(json.dumps(fixtures(),indent=2))
