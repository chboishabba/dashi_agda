"""Robust common-source endpoint contrast certificate on pinned SI carrier.
No environmental control parameters; synthetic observations only.
Usage: python check.py path/to/si_covariance.py
"""
import sys,hashlib,json
from pathlib import Path
import numpy as np
from scipy.optimize import minimize_scalar
raw=Path(sys.argv[1]).read_bytes()
assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='1a3a2df7892833ac4560d462c5d5843222767fff'
exec(compile(raw.decode().split('\nrows=[];maxledger=')[0],sys.argv[1],'exec'))
# Exact Schur certificate on an indefinite endpoint, with an unobserved mode.
q=sp.Matrix([[2,1],[1,-1]]);m=sp.Matrix([[1,0]]);lam=sp.Rational(1,2)
d=sp.Matrix([[2-lam+1/(lam+1)]])
r=lam*sp.eye(2)+m.T*d*m-q
assert r==sp.Matrix([[sp.Rational(2,3),-1],[-1,sp.Rational(3,2)]])
assert r.det()==0 and r.trace()>0
# Observer error delta and source trace cap I=1: covariance error <=
# epsilon + (2 ||M|| delta + delta^2). Here normalize ||M||=1.
# For every PSD S, tr S <=1, and ||MSM^H-Y||_F <= eta,
# H <= lambda I + M^H D M gives tr(HS) <= lambda+tr(DY)+eta||D||_F.
# For delta_H spectral error add delta_H, since tr S<=1.
def cert(H,M,Y,eta):
    scale=np.linalg.norm(H,2); H=H/scale
    U,s,W=np.linalg.svd(M,full_matrices=True);rank=int(sum(s>s[0]*1e-12));P=W[:rank].conj().T; F=W[rank:].conj().T
    V=U[:,:rank]/s[:rank];A=P.conj().T@H@P;K=F.conj().T@H@F;B=P.conj().T@H@F
    if F.shape[1]:
        ev,Q=np.linalg.eigh(K); B=B@Q; low=max(0.,ev[-1])+1e-10
    else:ev=np.array([]);low=1e-10
    def witness(l):
        S=A-l*np.eye(rank)+(B/(l-ev))@B.conj().T
        D=V@S@V.conj().T;D=(D+D.conj().T)/2
        # Recheck PSD on original coordinates, with numerical roundoff guard.
        defect=max(0.,-np.linalg.eigvalsh(l*np.eye(len(H))+M.conj().T@D@M-H)[0])+1e-12
        return l+defect+np.trace(D@Y).real+eta*np.linalg.norm(D,'fro')
    candidates=[witness(low),witness(1.+low)]
    fit=minimize_scalar(witness,bounds=(low,2.+low),method='bounded',options={'xatol':1e-12})
    candidates.append(witness(fit.x))
    # Independent universal certificate, D=0.
    candidates.append(max(0.,np.linalg.eigvalsh(H)[-1])+1e-12)
    return min(candidates)*scale
rho=1.68e-8;rows=[];rng=np.random.default_rng(369);checks=0
truth=np.eye(16,dtype=complex)[:,[0,1,3]]/np.sqrt(3);S=truth@truth.conj().T
frames={'center':angular(np.array([0.,0.,1.])), 'axes':np.vstack([angular(n)/np.sqrt(6) for n in np.vstack([np.eye(3),-np.eye(3)])])}
for f in (.005,.05,3.915,7.83):
    _,_,_,_,_,Z,V=shell(f);V=V/np.sqrt(kappa)
    for area in (1.,1e6):
        Hs=[]
        for aspect in (1.,1.5,(1+np.sqrt(5))/2):
            T=trace(area,aspect,np.pi/2);ell=R*np.linalg.norm(T[:,:3],axis=1)/np.sqrt(1.5)
            vol=5*np.sqrt(area)*1e-6;Rcu=np.diag(rho*ell*ell/(vol*ell/ell.sum()));Zp=T@Z@T.T/kappa;A=(Zp+Zp.conj().T)/2+Rcu;Vp=T@V
            Hs.append(Vp.conj().T@np.linalg.solve(A,Vp)/4)
        for name,B in frames.items():
            M=B@V;M=M/np.linalg.norm(M,2);Y=M@S@M.conj().T
            for label,H in zip(('3:2-square','phi-square'),(Hs[1]-Hs[0],Hs[2]-Hs[0])):
                H=(H+H.conj().T)/2;true=np.trace(H@S).real
                for err in (0.,1e-6,1e-4,1e-2):
                    # Nominal observer with bounded operator error, covariance noise,
                    # and endpoint matrix error, all separate assumed relative scales.
                    eta=err*np.linalg.norm(Y,'fro')+2*err+err*err;dh=err*np.linalg.norm(H,2)
                    lo=-cert(-H,M,Y,eta)-dh;hi=cert(H,M,Y,eta)+dh
                    assert lo<=true<=hi
                    # Random feasible source perturbations (convex mixtures); test only
                    # those satisfying declared observation residual, no empirical claim.
                    for j in range(4):
                        v=rng.normal(size=16)+1j*rng.normal(size=16);v/=np.linalg.norm(v);Rnew=(1-err/4)*S+(err/4)*np.outer(v,v.conj())
                        if np.linalg.norm(M@Rnew@M.conj().T-Y,'fro')<=eta+1e-14:
                            q=np.trace(H@Rnew).real
                            assert lo<=q-dh+1e-24 and q+dh<=hi+1e-24;checks+=1
                    rows.append(dict(f=f,area=area,observer=name,contrast=label,error=err,truth_W=float(true),lower_W=float(lo),upper_W=float(hi)))
print(json.dumps(dict(status='CONDITIONAL_ROBUST_SIGNED_ENDPOINT',rows=rows,feasible_checks=checks,physical_admission=False),indent=2))
