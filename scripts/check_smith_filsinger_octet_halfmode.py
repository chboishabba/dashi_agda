"""Reciprocal half-mode on LXXXIV one-cell ADE, transcribed original matrices.
Conditional scalar octet eigenchannel, not a layered dynamical Earth solve.
"""
import json
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
from scipy.optimize import minimize_scalar
R=s.Rational
A0=s.Matrix([[-R(1,10),R(1,2),0,-R(1,2)],[-R(2,3),0,0,0],[0,0,0,1],[R(3,2),0,-4,-R(2,3)]])
B0=s.Matrix([R(1,2),0,0,0]); M=s.diag(2,R(3,2),R(8,3),R(2,3))
assert M*A0+A0.T*M+s.diag(R(2,5),0,0,R(8,9))==s.zeros(4)
E,H,P,V,q,v,h,w,g,k,c,beta,m,Om,rq,rh,gl,jn,jp=s.symbols('E H P V q v h w g k c beta m Om rq rh gl jn jp',real=True)
d=R(3,2); z=s.Matrix([E,H,P,V]); U=(z.T*M*z)[0]/2
U+=(v*v+q*q/4+m*(w*w+Om*Om*h*h))/2+g*q*q*P+d*g*g*q**4/8+beta*q**4/4+k*q*q*P*P/(2*d)+c*q*q*h*h/2
f=A0*z+B0*(jn-gl*E); f[3]-=d*g*q*q+k*q*q*P
qa=-s.diff(U,q)-rq*v;ha=(jp-s.diff(U,h)-rh*w)/m
flow=sum(s.diff(U,x)*y for x,y in zip([E,H,P,V,q,v,h,w],list(f)+[v,qa,w,ha]))
assert s.expand(flow-(E*jn+jp*w-(R(1,5)+gl)*E*E-R(4,9)*V*V-rq*v*v-rh*w*w))==0
assert qa.subs({q:0,v:0})==0
# Linearized q about q=0. Fast-only h is the exact forced periodic oscillator.
def floquet(coef,T,r=.03):
    def rhs(t,y):return (np.array([[0,1],[-coef(t),-r]])@y.reshape(2,2)).ravel()
    sol=solve_ivp(rhs,(0,T),np.eye(2).ravel(),rtol=2e-11,atol=2e-13,max_step=T/100)
    assert sol.success
    F=sol.y[:,-1].reshape(2,2);err=abs(np.linalg.det(F)-np.exp(-r*T));assert err<1e-9
    return float(np.log(max(abs(np.linalg.eigvals(F))))/T),float(err)
fast=[]
for O in (20.,100.,7800/7.83):
 for amp in (.25,1.,2.):
    rate,err=floquet(lambda t:.25+.25*amp**2*np.cos(O*t)**2,np.pi/O)
    fast.append(dict(ratio=O,amplitude=amp,rate=rate,det_error=err))
assert all(r['rate']<0 for r in fast)
A=np.array(A0,float);B=np.array(B0,float).ravel();G=1/3;A[0,0]-=G/2
cubic=.5;octet=.2;damp=.03;quartic=1.
ph=np.linalg.solve(1j*np.eye(4)-A,B)
slow=[]
for g0 in (0.,cubic):
 for amp in (.05,.1,.25,.5,1.,2.):
    def coef(t):
        pp=amp*(ph[2]*np.exp(1j*t)).real
        return .25+2*g0*pp+octet*pp*pp/1.5
    rate,err=floquet(coef,2*np.pi,damp)
    slow.append(dict(cubic=g0,amplitude=amp,rate=rate,det_error=err))
Mnum=np.array(M,float)
def energy(y):
    z=y[:4];q,v=y[4:6];p=z[2]
    return z@Mnum@z/2+(v*v+q*q/4)/2+cubic*q*q*p+1.5*cubic*cubic*q**4/8+quartic*q**4/4+octet*q*q*p*p/3
# HF OFF here; autonomous q seeded from initial state, not a forced half tone.
def integrate(amp,seed,periods=240,rtol=2e-9):
    ini=np.r_[np.zeros(4),seed,0.,np.zeros(4)];T=2*np.pi*periods
    def rhs(t,y):
        E,H,P,V,q,v=y[:6];j=amp*np.cos(t);f=A@y[:4]+B*j;f[3]-=1.5*cubic*q*q+octet*q*q*P
        qa=-(.25+2*cubic*P+octet*P*P/1.5)*q-(1.5*cubic*cubic/2+quartic)*q**3-damp*v
        return np.r_[f,v,qa,E*j,G*E*E,.2*E*E+4/9*V*V,damp*v*v]
    sol=solve_ivp(rhs,(0,T),ini,rtol=rtol,atol=rtol/100,max_step=.15,dense_output=True)
    assert sol.success
    y=sol.y[:,-1];start=sol.sol(T-40*np.pi);W=y[6:]-start[6:];delta=energy(y)-energy(start);err=W[0]-sum(W[1:])-delta
    assert abs(err)<1e-5
    times=np.linspace(T-40*np.pi,T,4001);qs=sol.sol(times)[4];half=2*abs(np.trapezoid(qs*np.exp(-.5j*times),times))/(40*np.pi)
    return dict(amplitude=amp,seed=seed,half_amplitude=float(half),natural=float(W[0]/(40*np.pi)),load=float(W[1]/(40*np.pi)),native_heat=float(W[2]/(40*np.pi)),half_heat=float(W[3]/(40*np.pi)),storage_change=float(delta/(40*np.pi)),ledger_residual=float(err/(40*np.pi)),period2_return=float(np.linalg.norm(y[:6]-sol.sol(T-4*np.pi)[:6])))
branches=[integrate(a,b) for a in (.1,.5,1.) for b in (0.,1e-4)]
def passive(gl,k):
    aa=np.array(A0,float);aa[0,0]-=gl/2;aa[3,2]=-k
    e=np.linalg.solve(1j*np.eye(4)-aa,B)[0];return gl*abs(e)**2/2
opt=[]
for kk in (3.,4.,5.):
    sol=minimize_scalar(lambda g:-passive(g,kk),bounds=(1e-6,20),method='bounded');opt.append(dict(stiffness=kk,load_G=float(sol.x),power=float(-sol.fun)))
for row in branches:row['passive_same_load']=passive(G,4)*row['amplitude']**2;row['passive_best_sampled']=max(r['power'] for r in opt)*row['amplitude']**2
print(json.dumps(dict(status='CONDITIONAL_RECIPROCAL_HALF_MODE',fast=fast,slow=slow,branches=branches,passive=opt,scope='Transcribed original one-cell ADE; chosen cubic and positive scalar octet coupling. Fast-only linearized periodic branch; slow seeded runs HF off. No simultaneous multirate nonlinear branch, calibrated coefficients, actual HF conversion or solar extraction.'),indent=2))
