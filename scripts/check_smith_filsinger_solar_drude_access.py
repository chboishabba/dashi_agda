"""Conditional two-frequency magnetized Drude sheet on prior planar boundary.
No measured material or GAMERA data; thermal collision law is illustrative.
RMS phasors, per-area work. Local absorbed HF is a lower bound on driver cost.
"""
import json
import numpy as np
import sympy as s
from scipy.optimize import brentq
mu=4*np.pi*1e-7; eps=8.8541878128e-12
J=np.array([[0.,-1.],[1.,0.]])
# Drude kinetic sheet energy: K=|j|^2/(2D), j'=D E-nu j+wc J j.
x,y,ex,ey,D,nu,wc=s.symbols('x y ex ey D nu wc',real=True)
j=s.Matrix([x,y]);E=s.Matrix([ex,ey]);Js=s.Matrix([[0,-1],[1,0]])
assert s.expand(j.dot(D*E-nu*j+wc*Js*j)/D-j.dot(E)+nu*j.dot(j)/D)==0
# General complex source-port maximum power: H is Hermitian real part.
a,b,c,d=s.symbols('a b c d',real=True);r,t=s.symbols('r t',positive=True)
assert s.expand(a*c+b*d-r*c*c-t*d*d-(a*a/(4*r)+b*b/(4*t)-r*(c-a/(2*r))**2-t*(d-b/(2*t))**2))==0

def sheet(f,nu,wc,D):
    return D*np.linalg.inv((nu+2j*np.pi*f)*np.eye(2)-wc*J)
def solve(f,lam,sigma,nu,wc,D,ei):
    w=2*np.pi*f;k=2*np.pi/(lam*1000);ya=1/(mu*1e6)
    def adm(cond):
        q=np.sqrt(complex(k*k+1j*w*mu*cond-w*w*mu*eps))
        return q,np.array([(cond+1j*w*eps)/q,q/(1j*w*mu)])
    qa,Y=adm(0);_,Yg0=adm(sigma);Yg=np.diag(Yg0)
    C=np.eye(2)*np.cosh(qa*110e3);Dair=np.diag(np.sinh(qa*110e3)/Y);F=np.diag(np.sinh(qa*110e3)*Y)
    S=sheet(f,nu,wc,D);U=ya*np.eye(2)+S
    M=U@(C+Dair@Yg)+F+C@Yg;N=U@Dair+C
    Z=np.linalg.solve(M,N);V=np.linalg.solve(M,2*ya*ei);H=(Z+Z.conj().T)/2
    assert np.linalg.eigvalsh(H).min()>0
    jl=np.linalg.solve(H,V)/2;eg=V-Z@jl;hg=Yg@eg+jl;es=C@eg+Dair@hg;hs=F@eg+C@hg
    inc=ya*np.vdot(ei,ei).real;ref=ya*np.vdot(es-ei,es-ei).real
    js=S@es;ion=np.vdot(es,js).real;heat=nu*np.vdot(js,js).real/D
    soil=np.vdot(eg,Yg@eg).real;load=np.vdot(jl,eg).real
    assert abs(ion-heat)<1e-10 and abs(inc-ref-ion-soil-load)<1e-9
    assert np.linalg.norm(eg-Z.conj().T@jl)<1e-8
    assert abs(load-np.vdot(V,np.linalg.solve(H,V)).real/4)<1e-10
    return dict(incident=float(inc),reflected=float(ref),natural_net=float(inc-ref),ion=float(ion),soil=float(soil),load=float(load),residual=float(inc-ref-ion-soil-load),ground_E=[[float(v.real),float(v.imag)] for v in eg])
# Collision rate increases with temperature surrogate theta. Thermal equilibrium:
# ell*theta = LF Drude heat + absorbed HF heat. D and wc stay fixed.
# ell chosen relative to normalized upper incident power, not fitted to a site.
rows=[];controls=0;maxres=0.;maxtherm=0.
for f in (.005,.05):
 for lam in (1000,10000):
  for sigma in (.001,.01):
   for ratio in (.25,1.,4.):
    wc0=1e5;nu0=ratio*wc0;D0=5*(nu0**2+wc0**2)/nu0
    for pol,ei in [('TM',np.array([1,0],complex)),('TE',np.array([0,1],complex)),('right',np.array([1,1j])/np.sqrt(2)),('left',np.array([1,-1j])/np.sqrt(2))]:
     inc=1/(mu*1e6)
     def state(theta):return solve(f,lam,sigma,nu0*(1+theta),wc0,D0,ei)
     # All roots in selected interval located by bracket grid; not universal proof.
     for ellratio in (.05,.5,5.):
      ell=ellratio*inc
      grid=np.r_[0.,np.geomspace(1e-5,32,100)]
      def balance(t):return ell*t-state(t)['ion']
      vals=[balance(t) for t in grid];roots=[]
      for a,b,fa,fb in zip(grid[:-1],grid[1:],vals[:-1],vals[1:]):
       if fa*fb<0:roots.append(brentq(balance,a,b,xtol=1e-13))
      assert roots
      cold=max(roots,key=lambda t:state(t)['load']);C=state(cold)
      for theta in (cold,cold+.25,cold+.5,cold+1,cold+2,cold+4):
       W=state(theta);pump=ell*theta-W['ion'];maxres=max(maxres,abs(W['residual']))
       if pump< -1e-10:continue
       pump=max(0.,pump);Sh=sheet(7800,nu0*(1+theta),wc0,D0)
       # chosen local circular HF polarization maximizing dissipative admittance
       ev,vec=np.linalg.eigh((Sh+Sh.conj().T)/2);gain=float(ev[-1]);assert gain>0
       hf_rms=np.sqrt(pump/gain);B_pump=ell*theta # source-off, same thermal state
       for paid in (pump,B_pump):
        eh=vec[:,-1]*np.sqrt(paid/gain);jh=Sh@eh
        assert abs(np.vdot(eh,jh).real-paid)<1e-10
        assert abs(nu0*(1+theta)*np.vdot(jh,jh).real/D0-paid)<1e-10
       off=solve(f,lam,sigma,nu0*(1+theta),wc0,D0,np.zeros(2,complex));assert off['load']==off['ion']==off['natural_net']==0
       maxtherm=max(maxtherm,abs(ell*theta-W['ion']-pump));controls+=1
       rows.append(dict(f=f,lambda_km=lam,soil=sigma,ratio=ratio,polarization=pol,ell_over_inc=ellratio,theta_passive=cold,theta=theta,passive=C['load']/inc,load=W['load']/inc,net=(W['load']-pump)/inc,delta_net=(W['load']-pump-C['load'])/inc,delta_access=(W['natural_net']-C['natural_net'])/inc,pump=pump/inc,hf_local_rms=float(hf_rms),source_off_pump=B_pump/inc,source_off_load=0.,passive_roots=len(roots)))
# Actual low-frequency linear Drude response independent of HF when theta fixed.
# No source attribution from the heating fixture alone.
active=[r for r in rows if r['theta']>r['theta_passive']+1e-8]
best=max(active,key=lambda r:r['delta_net']);gain=[r for r in active if r['delta_net']>1e-10];both=[r for r in gain if r['delta_access']>1e-10]
print(json.dumps(dict(status='CONDITIONAL_DRUDE_THERMAL_ACCESS',rows=len(rows),active=len(active),source_off_controls=controls,source_off_A='zero theta and zero fields; zero thermal work',gross_load_improvement=sum(r['load']>r['passive']+1e-10 for r in active),increased_natural_access=sum(r['delta_access']>1e-10 for r in active),positive_absolute_net=sum(r['net']>1e-10 for r in active),positive_vs_matched_equilibrium=len(gain),positive_and_increased_access=len(both),max_energy_residual=maxres,max_thermal_residual=maxtherm,best=best,best_gross=max(active,key=lambda r:r['load']-r['passive']),best_access=max(active,key=lambda r:r['delta_access']),max_load=max(active,key=lambda r:r['load']),scope='Same planar surrogate as P1, full two-polarization passive conjugate load at each theta, thermal equilibrium roots bracketed not proved unique. Thermal law/coefficients assumed, local HF absorption lower bound on transmitter work, no propagation/calibration, no finite receiver, no physical extraction. Positive comparison if any is against matched passive equilibrium branches sampled, not all possible passive materials or thermal designs.'),indent=2))
