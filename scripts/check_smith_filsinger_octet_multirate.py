"""Reciprocal rotating-wave model on pinned half-mode ADE; conditional only."""
import hashlib,json,sys
from pathlib import Path
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
from scipy.optimize import minimize_scalar
from functools import lru_cache
path=Path(sys.argv[1]);raw=path.read_bytes()
assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='260ac395c6e65cfdf65c880d7a913fe979e39032'
ns={};exec(compile(raw.decode().split('fast=[]')[0],str(path),'exec'),ns)
A0=np.array(ns['A0'],float);B=np.array(ns['B0'],float).ravel();M=np.array(ns['M'],float)
G=1/3;A=A0.copy();A[0,0]-=G/2;g=.5;k=.2;c=.25;rq=.03;beta=1.;d=1.5
q,v,x,y,cc,rate,a,O=s.symbols('q v x y c rate a O',real=True)
W=(1+cc*q*q/2)*(x*x+y*y)/2
xd=cc*q*q*O*y/2+rate*(a-x);yd=-cc*q*q*O*x/2-rate*y
assert s.expand(s.diff(W,q)*v+s.diff(W,x)*xd+s.diff(W,y)*yd-(cc*q*v*(x*x+y*y)/2+(1+cc*q*q/2)*rate*(a*x-x*x-y*y)))==0
e,j,r=s.symbols('e j r',real=True,nonzero=True)
assert s.expand(j*e-r*e**2-(j**2/(4*r)-r*(e-j/(2*r))**2))==0

def energy(y,exact,bias):
    z=y[:4];q,v,x,hv=y[4:8];p=z[2]
    slow=z@M@z/2+(v*v+q*q*(.25+bias))/2+g*q*q*p+d*g*g*q**4/8+beta*q**4/4+k*q*q*p*p/(2*d)
    if exact:return slow+(x*x+hv*hv)/2+c*q*q*x*x/2
    return slow+(1+c*q*q/2)*(x*x+hv*hv)/2

@lru_cache(None)
def run(src,amp,ratio,Q,periods=80,exact=False,bias=0.,seed=1e-4):
    rate=ratio/(2*Q);T=2*np.pi*periods;window=2*np.pi*min(20,periods//2)
    ini=np.r_[np.zeros(4),seed,0.,amp,0.,np.zeros(6)]
    def rhs(t,y):
        E,H,P,V,q,v,x,b=y[:8];jn=src*np.cos(t);f=A@y[:4]+B*jn;f[3]-=d*g*q*q+k*q*q*P
        if exact:
            h2=x*x;xd=ratio*b;yd=-ratio*(1+c*q*q)*x-2*rate*b-2*rate*amp*np.sin(ratio*t)
            pump=-2*rate*amp*np.sin(ratio*t)*b;heat=2*rate*b*b
        else:
            h2=(x*x+b*b)/2;xd=c*q*q*ratio*b/2+rate*(amp-x);yd=-c*q*q*ratio*x/2-rate*b
            pump=(1+c*q*q/2)*rate*amp*x;heat=(1+c*q*q/2)*rate*(x*x+b*b)
        qa=-(.25+bias+2*g*P+k*P*P/d+c*h2)*q-(d*g*g/2+beta)*q**3-rq*v
        return np.r_[f,v,qa,xd,yd,E*jn,G*E*E,.2*E*E+4/9*V*V,rq*v*v,pump,heat]
    sol=solve_ivp(rhs,(0,T),ini,method='DOP853',rtol=2e-9,atol=2e-11,max_step=(.3/ratio if exact else .35),dense_output=True)
    assert sol.success
    end=sol.y[:,-1];start=sol.sol(T-window);w=(end[8:]-start[8:])/window;delta=(energy(end,exact,bias)-energy(start,exact,bias))/window
    err=w[0]+w[4]-w[1]-w[2]-w[3]-w[5]-delta;assert abs(err)<2e-7
    times=np.linspace(T-window,T,2001);qs=sol.sol(times)[4];half=2*abs(np.trapezoid(qs*np.exp(-.5j*times),times))/window
    return dict(src=src,amp=amp,ratio=ratio,Q=Q,periods=periods,exact=exact,bias=bias,half=float(half),natural=float(w[0]),load=float(w[1]),native_heat=float(w[2]),half_heat=float(w[3]),pump=float(w[4]),fast_heat=float(w[5]),storage_rate=float(delta),ledger_error=float(err),net_storage_adjusted=float(w[1]-w[4]+min(delta,0.)),q_return=float(np.linalg.norm(end[:6]-sol.sol(T-4*np.pi)[:6])),fast_end_norm=float(np.linalg.norm(end[6:8])))

def passive(gl,stiff):
    aa=A0.copy();aa[0,0]-=gl/2;aa[3,2]=-stiff
    e=np.linalg.solve(1j*np.eye(4)-aa,B)[0];return gl*abs(e)**2/2
best=max(-minimize_scalar(lambda gl:-passive(gl,stiff),bounds=(1e-6,20),method='bounded').fun for stiff in (3.,4.,5.))
rows=[]
for ratio,Q in ((20.,100.),(7800/7.83,100.),(7800/7.83,10000.)):
    for src in (.5,1.):
        C=run(src,0.,ratio,Q)
        for amp in (.5,1.):
            D=run(src,amp,ratio,Q);Boff=run(0.,amp,ratio,Q);Aoff=run(0.,0.,ratio,Q)
            S=run(src,0.,ratio,Q,bias=c*amp*amp/2)
            rows.append(dict(A=Aoff,B=Boff,C=C,D=D,static_bias=S,static_best=best*src*src,delta_same_load=D['net_storage_adjusted']-C['net_storage_adjusted'],delta_static_bias=D['net_storage_adjusted']-S['net_storage_adjusted'],delta_best=D['net_storage_adjusted']-best*src*src))
bench=[]
for src,amp in ((.5,.5),(1.,1.)):
    av=run(src,amp,20.,100.,periods=20);ex=run(src,amp,20.,100.,periods=20,exact=True)
    bench.append(dict(averaged=av,exact=ex,difference={k:av[k]-ex[k] for k in ('half','load','pump','net_storage_adjusted')}))
print(json.dumps(dict(status='CONDITIONAL_RECIPROCAL_MULTIRATE',rows=rows,benchmark=bench,passive_best_unit=best,scope='Averaged rotating-wave surrogate with exact model energy ledger and precharged fast storage. Direct ratio20 finite horizon check only. No uniform averaging theorem, physical HF delivery, actual source access change or solar extraction.'),indent=2))
