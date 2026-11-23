"""Exact midpoint/SBP algebra and time-windowed Weyl receiver, same F8 action."""
import sympy as s
import numpy as np
from scipy.special import spherical_jn
from math import sqrt
from check_f8_midpoint_action import Midpoint

def exact():
    n=2;vec=lambda a:s.Matrix(s.symbols(a+':2'))
    q,u,f=map(vec,('q','u','f'));v,dt=s.symbols('v dt')
    C=s.Matrix(n,n,s.symbols('c:4'));A=s.Matrix([[s.Symbol('a0'),s.Symbol('a1')],[s.Symbol('a1'),s.Symbol('a2')]])
    D=s.Matrix([[s.Symbol('d0'),s.Symbol('d1')],[s.Symbol('d1'),s.Symbol('d2')]])
    du=dt*q;dm=dt*(-v*C.T*q-A*u-D*q+f)
    delta=(q.T*(dm+v*C*du)+u.T*A*du)[0]
    assert s.expand(delta-dt*(q.T*f-q.T*D*q)[0])==0
    for N in (2,3,7):
        a=s.symbols('a:'+str(N));u=s.symbols('U:'+str(N+1))
        assert s.expand(sum(a[j]*(u[j+1]-u[j]) for j in range(N))-a[-1]*u[-1]+a[0]*u[0]+sum((a[j]-a[j-1])*u[j] for j in range(1,N)))==0
    print('PASS exact midpoint polarized energy and discrete boundary summation by parts (3 lengths)',flush=True)

def run():
    S=Midpoint(90,10,3,.01);dt=S.dt;N=S.nt;times=np.arange(N+1)*dt
    x=np.zeros((2,S.fe.n,S.n));hist=[x[0,0].copy()];max_trace=0.
    Ctr=8*(1+S.fe.Y[-1])**3
    for i in range(N):
        x,q=S.advance(x,2*i+1);hist.append(x[0,0].copy())
        e=S.energy(x,2*i+2);max_trace=max(max_trace,np.max(S.k*hist[-1]**2/(Ctr*e+1e-300)))
    assert max_trace<=1+1e-10
    U=np.array(hist);r=S.r;k=S.k
    sl=sum(d*k**4*spherical_jn(l,k*r) for d,l in zip((.4,-4/7,1/35),(0,2,4)))
    # Smooth compact temporal window strictly inside evolution. Fixed comoving r.
    center=times[-1]-.15;half=.10;z=(times-center)/half;chi=np.zeros(N+1);inside=abs(z)<1
    chi[inside]=np.exp(1-1/(1-z[inside]**2));chi/=dt*chi.sum()
    b=np.array([S.stage[2*j][3] for j in range(N+1)]);t=1/b;V=np.sqrt(1+t*t)/t;J=-1/(t*np.sqrt(1+t*t));
    d1=(U[2:]-U[:-2])/(2*dt);d2=(U[2:]-2*U[1:-1]+U[:-2])/dt**2
    for label,fac,extra,spatial in [('E4',.25,0,1),('E5_SMS',.5,2,-1)]:
        a2=-fac*b*b*V*V*chi;a1=-fac*b*b*(J+extra*V)*chi;a0=fac*b*b*spatial*chi
        direct=dt*sl*np.sum(a2[1:-1,None]*d2+a1[1:-1,None]*d1+a0[1:-1,None]*U[1:-1]*k*k,axis=0)
        w=np.zeros_like(U);w[1:-1]+=a0[1:-1,None]*k*k;w[:-2]+=a2[1:-1,None]/dt**2-a1[1:-1,None]/(2*dt);w[1:-1]-=2*a2[1:-1,None]/dt**2;w[2:]+=a2[1:-1,None]/dt**2+a1[1:-1,None]/(2*dt)
        byparts=dt*sl*np.sum(w*U,axis=0);err=np.linalg.norm(direct-byparts)/np.linalg.norm(direct);assert err<1e-10
        print(label,'windowed response',direct.sum(),'SBP relative defect',err,flush=True)
    print('max trace bound utilization',max_trace,flush=True)
if __name__=='__main__':exact();run()
