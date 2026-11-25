"""Conditional l=1 TE/TM layered spherical boundary, RMS exp(i omega t).
Uses pinned OCT369 angular donor. No calibrated solar source or HF actuator.
"""
import hashlib,json,runpy,sys
from pathlib import Path
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp,quad_vec
raw=Path(sys.argv[1]).read_bytes(); blob=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
assert blob=='1f493bdedf3ca058470db4fe0154c13d4df905b4'
d=runpy.run_path(sys.argv[1]); weights={1:1/21,2:4/105,3:9/280}
# Orthonormal tangent dipoles, ordered TE(T), TM(P), each x,y,z.
G=np.zeros((6,6));K=G.copy();J=G.copy();axis=np.ones(3)/np.sqrt(3)
for site in d['punctured27']:
    n=np.array(site)/np.linalg.norm(site);w=weights[sum(x!=0 for x in site)]
    N=np.cross(n,np.eye(3)).T;B=np.sqrt(1.5)*np.column_stack((N,np.eye(3)-np.outer(n,n)))
    G+=w*B.T@B;K+=w*(axis@n)*B.T@B;J+=w*B.T@N@B
assert np.max(abs(G-np.eye(6)))<1e-14
assert np.max(abs(K-K.T))<1e-14 and np.max(abs(J+J.T))<1e-14
assert np.max(abs(K[:3,:3]))<1e-14 and np.max(abs(K[3:,3:]))<1e-14
# Power-conjugate radial e=rE_t, h=r(H cross n)_t. TM radial electric field
# coefficient has magnitude sqrt(l(l+1))*|h|/(|A| r^2) in normalized modes.
sig,eps,mu,om,r,L=s.symbols('sigma epsilon mu omega r L',positive=True,real=True)
A=sig+s.I*om*eps
for typ in ('TE','TM'):
    e,h=s.symbols('e h',complex=True)
    a,b=(s.I*om*mu,A+L/(s.I*om*mu*r*r)) if typ=='TE' else (s.I*om*mu+L/(A*r*r),A)
    deriv=s.re(s.conjugate(-a*h)*h+s.conjugate(e)*(-b*e))
    loss=sig*s.Abs(e)**2+(0 if typ=='TE' else sig*L*s.Abs(h)**2/(s.Abs(A)**2*r*r))
    assert s.simplify(deriv+loss)==0
# Same Lorentz polarization parameters as original LXXXIV A[2:4,2:4],
# A[3,0]=3/2: (4-w^2+i(2/3)w)P=(3/2)E. Dimensionless donor,
# not physical SI calibration. Use passive sheet oscillator at separate clock.
w=s.symbols('w',positive=True,real=True)
Y=s.I*w*s.Rational(3,2)/(4-w*w+s.I*s.Rational(2,3)*w)
assert s.simplify(s.re(Y)-w*w/((4-w*w)**2+4*w*w/9))==0
MU=4*np.pi*1e-7; EP=8.8541878128e-12;R=6371000.; H=110000.;ya=1/(MU*1e6)
# h scaled by reference admittance, preserving power ya Re(e* hscaled).
def layer(f,r0,r1,sigma,typ):
    w=2*np.pi*f;A=sigma+1j*w*EP
    def mat(r):
        a,b=(1j*w*MU,A+2/(1j*w*MU*r*r)) if typ=='TE' else (1j*w*MU+2/(A*r*r),A)
        return np.array([[0,-a*ya],[-b/ya,0]],complex)
    sol=solve_ivp(lambda r,t:(mat(r)@t.reshape(2,2)).ravel(),(r0,r1),np.eye(2,dtype=complex).ravel(),rtol=2e-11,atol=2e-12,dense_output=True)
    assert sol.success
    return sol
rows=[];maxerr=0.;maxrad=0.;maxmatch=0.
for f in (.005,.05,3.915,7.83):
 for sigair in (0.,1e-9):
    layers=[(R,R+H/2,0.),(R+H/2,R+H,sigair)]
    sols={typ:[layer(f,*v,typ) for v in layers] for typ in ('TE','TM')}
    mats={typ:sols[typ][1].y[:,-1].reshape(2,2)@sols[typ][0].y[:,-1].reshape(2,2) for typ in sols}
    A,B,C,D=[np.diag(np.repeat([mats[t][i,j] for t in ('TE','TM')],3)) for i,j in ((0,0),(0,1),(1,0),(1,1))]
    # Inner resistive sheet ground termination; not a conducting Earth solve.
    for yg in (.1,1.,10.):
     for anis,hall in ((0.,0.),(.5,0.),(.5,1.)):
      # Dimensionless oscillator clock normalized at 7.83 Hz, assumed scale.
      z=f/7.83;yl=1j*z*1.5/(4-z*z+1j*2*z/3)
      S=2*(np.eye(6)+anis*K)+hall*J+yl*np.eye(6)
      assert np.linalg.eigvalsh((S+S.conj().T)/2).min()>0
      U=np.eye(6)+S;M=U@(A-B*yg)-(C-D*yg);N=D-U@B
      Z=np.linalg.solve(M,N);Hr=(Z+Z.conj().T)/2
      assert np.linalg.eigvalsh(Hr).min()>0
      # fixed amplitude modal sources: separate solar-labelled TE and lightning-labelled TM,
      # at same chosen frequency only. Relative phases are synthetic controls.
      es=np.array([1,0,0,0,0,0],complex);el=np.array([0,0,0,0,1,0],complex)
      for phase in (0.,np.pi/2,np.pi):
       ei=es+np.exp(1j*phase)*el;V=np.linalg.solve(M,2*ei);j=np.linalg.solve(Hr,V)/2
       e0=V-Z@j;h0=-yg*e0-j;e1=A@e0+B@h0;h1=C@e0+D@h0
       inc=np.vdot(ei,ei).real;ref=np.vdot(e1-ei,e1-ei).real
       sheet=np.vdot(e1,S@e1).real;ground=yg*np.vdot(e0,e0).real;load=np.vdot(e0,j).real
       heat=0.
       for typ,sl in (('TE',slice(0,3)),('TM',slice(3,6))):
        state=np.stack((e0[sl],h0[sl]))
        for (r0,r1,sg),sol in zip(layers,sols[typ]):
         w=2*np.pi*f;Ac=sg+1j*w*EP
         def dens(r):
            ee,hh=sol.sol(r).reshape(2,2)@state
            return sg/ya*(np.vdot(ee,ee).real+(2*ya**2*np.vdot(hh,hh).real/(abs(Ac)**2*r*r) if typ=='TM' else 0))
         heat+=float(quad_vec(dens,r0,r1,epsabs=1e-11,epsrel=1e-9)[0]);state=sol.y[:,-1].reshape(2,2)@state
       rad=np.vdot(e0,h0).real-np.vdot(e1,h1).real-heat;err=inc-ref-sheet-ground-load-heat
       match=np.linalg.norm(e0-Z.conj().T@j)
       maxrad=max(maxrad,abs(rad));maxerr=max(maxerr,abs(err));maxmatch=max(maxmatch,match)
       assert abs(err)<2e-7 and abs(rad)<2e-7 and match<2e-7
       # linear source decomposition at fixed selected load j=L V where L=Hr^-1/2 (factor 1/2).
       Vs=np.linalg.solve(M,2*es);Vl=np.linalg.solve(M,2*el)
       cap=lambda v: np.vdot(v,np.linalg.solve(Hr,v)).real/4
       cross=load-cap(Vs)-cap(Vl)
       assert abs(cross-.5*np.real(np.exp(1j*phase)*np.vdot(Vs,np.linalg.solve(Hr,Vl))))<1e-7
       rows.append(dict(f=f,sigair=sigair,ground=yg,anis=anis,hall=hall,phase=phase,load_fraction=load/inc,solar_only=cap(Vs),lightning_only=cap(Vl),cross=cross,sheet_heat=sheet/inc,radial_heat=heat/inc))
print(json.dumps(dict(status='CONDITIONAL_LAYERED_SPHERE_TE_TM',donor_blob=blob,cases=len(rows),max_energy_residual=maxerr,max_radial_residual=maxrad,max_match_error=maxmatch,mix_eigenvalues=np.linalg.eigvalsh(K).tolist(),best=max(rows,key=lambda a:a['load_fraction']),max_cross=max(rows,key=lambda a:abs(a['cross'])),rows=rows,scope='l=1 Galerkin only, higher modes omitted; normalized upper admittance and lower resistive sheet, two air layers, assumed passive Lorentz sheet, synthetic source phases and common-frequency labels. No physical solar conversion or actual HF control.'),indent=2))
