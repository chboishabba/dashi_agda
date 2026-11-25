"""Source covariance fibre bounds for signed SI receiver endpoint contrasts.
Consumes pinned 16-mode shell. Synthetic observations only; no plasma activation.
Usage: python check.py /path/to/check_smith_filsinger_solar_si_covariance.py
"""
import sys,hashlib,json
from pathlib import Path
import numpy as np
from scipy.optimize import brentq
raw=Path(sys.argv[1]).read_bytes()
assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='1a3a2df7892833ac4560d462c5d5843222767fff'
exec(compile(raw.decode().split('\nrows=[];maxledger=')[0],sys.argv[1],'exec'))
# Maximize a Hermitian form on all PSD source covariances with exact observed
# covariance and trace <= 1 W. Factor is padded to 16 columns; right-unitary
# alignment makes the observed factor fixed, even when hidden rank increases.
def support(H,U0,F):
    scale=np.linalg.norm(H,2)
    if scale==0:return 0.,0.,0.
    H=H/scale; a=np.trace(U0.conj().T@H@U0).real
    r2=max(0.,1-np.linalg.norm(U0,'fro')**2)
    if F.shape[1]==0 or r2<1e-25:return a*scale,a*scale,0.
    K=F.conj().T@H@F; d,Q=np.linalg.eigh(K); b=Q.conj().T@F.conj().T@H@U0
    floor=max(0.,d[-1]); r=np.sqrt(r2)
    # Max quadratic over Frobenius ball: lambda >= max(0,lambda_max K).
    # Strictly positive shift gives a valid dual even in the hard case.
    eps=1e-12; low=floor+eps
    def x(lam):return b/(lam-d)[:,None]
    if np.linalg.norm(x(low))>r:
        hi=max(1.,2*low)
        while np.linalg.norm(x(hi))>r:hi*=2
        lam=brentq(lambda l:np.linalg.norm(x(l))-r,low,hi,xtol=1e-14)
        X=x(lam); X*=min(1.,r/np.linalg.norm(X))
    else:
        lam=low; X=x(lam)
        if floor>0:
            # hard case: use a padded zero observation column, orthogonal to X
            assert np.linalg.norm(b[:,-1])<1e-12
            X[-1,-1]=np.sqrt(max(0.,r2-np.linalg.norm(X)**2))
    primal=a+2*np.vdot(X,b).real+np.sum(d[:,None]*abs(X)**2)
    dual=a+lam*r2+np.sum(abs(b)**2/(lam-d)[:,None])
    assert primal<=dual+1e-10 and dual-primal<1e-8
    U=U0+F@Q@X
    assert np.linalg.norm(U,'fro')**2<=1+1e-10
    assert abs(np.trace(U.conj().T@H@U).real-primal)<1e-10
    return float(primal*scale),float(dual*scale),float((dual-primal)*scale)

# Exact objective-fibre test (Hermitian, including indefinite contrasts).
H0=sp.diag(1,-1,0); M0=sp.Matrix([[1,0,0]])
assert H0*sp.Matrix([0,1,0])!=sp.zeros(3,1)
assert (sp.Matrix([[1,0,0]]).T*sp.Matrix([[1,0,0]]))*sp.Matrix([0,1,0])==sp.zeros(3,1)
# Uniform axial sampling versus existing full OCT quadrature (not site design).
axes=np.vstack([np.eye(3),-np.eye(3)])
oct=[];weights=[]
for p in product((-1,0,1),repeat=3):
    nn=sum(x!=0 for x in p)
    if nn:oct.append(np.array(p)/np.sqrt(nn));weights.append({1:1/21,2:4/105,3:9/280}[nn])
frames={'center_E':angular(np.array([0.,0.,1.])),
        'center_E_H':np.vstack([angular(np.array([0.,0.,1.])), -yg*angular(np.array([0.,0.,1.]))]),
        'six_axes_E':np.vstack([angular(n)/np.sqrt(6) for n in axes]),
        'OCT26_E':np.vstack([np.sqrt(w)*angular(n) for n,w in zip(oct,weights)])}
assert np.linalg.norm(frames['OCT26_E'].T@frames['OCT26_E']-np.eye(16))<1e-13
rho=1.68e-8;rows=[];maxgap=0.;maxcond=0.
# 1 W global incident covariance, three distinct synthetic modal states.
truth=np.zeros((16,16),complex);truth[:,0:3]=np.eye(16)[:,[0,1,3]]/np.sqrt(3)
for f in (.005,.05,3.915,7.83):
    _,_,_,_,_,Z,V=shell(f); V=V/np.sqrt(kappa)
    for area in (1.,1e6):
        objectives=[]
        for aspect in (1.,1.5,(1+np.sqrt(5))/2):
            T=trace(area,aspect,np.pi/2);ell=R*np.linalg.norm(T[:,:3],axis=1)/np.sqrt(1.5)
            vol=5*np.sqrt(area)*1e-6;Rcu=np.diag(rho*ell*ell/(vol*ell/ell.sum()))
            Zp=T@Z@T.T/kappa;H=(Zp+Zp.conj().T)/2+Rcu;Vp=T@V
            obj=Vp.conj().T@np.linalg.solve(H,Vp)/4;obj=(obj+obj.conj().T)/2
            assert np.linalg.eigvalsh(obj)[0]>-1e-12*np.linalg.norm(obj,2)
            objectives.append(obj)
        for name,Aobs in frames.items():
            M=Aobs@V; U,sv,W=np.linalg.svd(M,full_matrices=True);rank=int(sum(sv>sv[0]*1e-12));P=(W[:rank].conj().T/sv[:rank])@U[:,:rank].conj().T;F=W[rank:].conj().T
            Y=M@truth; U0=P@Y
            assert np.linalg.norm(M@U0-Y)<1e-10
            assert np.linalg.norm(M@F)<1e-10
            maxcond=max(maxcond,float(sv[0]/sv[rank-1]))
            for label,H in [('square',objectives[0]),('3:2-minus-square',objectives[1]-objectives[0]),('phi-minus-square',objectives[2]-objectives[0])]:
                val=float(np.trace(truth.conj().T@H@truth).real)
                mp,hi,g1=support(H,U0,F);np_,neglo,g2=support(-H,U0,F);lo=-neglo
                maxgap=max(maxgap,g1,g2)
                tol=1e-10*np.linalg.norm(H,2)
                assert lo-tol<=val<=hi+tol
                defect=float(np.linalg.norm(H@F,2)/np.linalg.norm(H,2)) if F.shape[1] else 0.
                rows.append(dict(f=f,area=area,observer=name,rank=rank,objective=label,truth_W=val,lower_W=lo,upper_W=hi,inner_lower_W=-np_,inner_upper_W=mp,relative_endpoint_dark_defect=defect))
print(json.dumps(dict(status='CONDITIONAL_SI_SIGNED_COVARIANCE_FIBRE',rows=rows,max_dual_gap_W=maxgap,max_observer_condition=maxcond,physical_admission=False),indent=2))
