"""S1 uncertain observation and covariance fibre on pinned receiver.
Args: S1, finite-return, current-budget, aperture, metric-charge scripts.
Synthetic normalized observations, not field measurements.
"""
import sys,json,hashlib
from pathlib import Path
import numpy as np
import sympy as s
paths=sys.argv[1:6]
raw=Path(paths[0]).read_bytes()
assert hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()=='3fd8dc6a93bafcdbebae9b570713f9c9f2e6e164'
old=sys.argv;sys.argv=paths;d={};exec(compile(raw.decode().split('\nrows=[];N=48')[0],paths[0],'exec'),d);sys.argv=old
# The pinned S1 prefix checks and executes all four underlying donors.
env=d['env'];N=48;B=env['angular'](np.array([0.,0.,1.]),N)[:2]
# Exact covariance labels can be repartitioned without changing any observer.
a,b,alpha=s.symbols('a b alpha',real=True);C=s.Matrix([[a*a,a*b],[a*b,b*b]])
assert (alpha*C+(1-alpha)*C-C).applyfunc(s.expand)==s.zeros(2)
assert s.expand((alpha*C).det())==0

def fibre(M,t):
    U,sv,W=np.linalg.svd(M,full_matrices=True);rank=int(sum(sv>sv[0]*1e-12))
    pinv=(W[:rank].conj().T/sv[:rank])@U[:,:rank].conj().T;F=W[rank:].conj().T
    assert np.linalg.norm(M@F)<1e-10
    assert np.linalg.norm(pinv@M+F@F.conj().T-np.eye(N))<1e-10
    return pinv,F,rank

def bound(M,t,y,eps,I):
    P,F,rank=fibre(M,t);u0=P@y;c=t@u0
    minnorm=max(0.,np.linalg.norm(u0)-eps*np.linalg.norm(P,2))
    if minnorm>np.sqrt(I):return None
    radius=eps*np.linalg.norm(t@P)+np.linalg.norm(t@F)*np.sqrt(max(0.,I-minnorm**2))
    return max(0.,abs(c)-radius)**2,(abs(c)+radius)**2,float(radius),rank

rows=[];covrows=[];ranks=[];checks=0;rng=np.random.default_rng(369)
for f in (.005,.05,3.915,7.83):
    A,Bmat,Cmat,D,S,Z,V=env['shell'](f,N);T=env['overlap'](1.,1.,N)
    Y=np.column_stack([env['native'](f,e,1.)[0] for e in np.eye(7)])
    Rport=np.linalg.solve(np.eye(7)+T@Z@T.T@Y,T@V)
    w=f/7.83;t=np.sqrt(.52)*(np.linalg.solve(1j*w*np.eye(9)-env['Ac'],env['beta']*env['rad']*env['Kc'].T@env['L'].T/2)[-1]@Rport)
    M=B@V;Mh=-env['yg']*M
    Mtop=B@(A-Bmat*env['yg'])@V;Htop=B@(Cmat-D*env['yg'])@V
    r0=fibre(M,t)[2];r1=fibre(np.vstack((M,Mh)),t)[2];r2=fibre(np.vstack((M,Mtop,Htop)),t)[2]
    assert r0==r1==2
    ranks.append(dict(f=f,local_E=r0,local_E_H=r1,local_plus_upper_E_H=r2))
    for src in (0,4):
        truth=np.eye(N,dtype=complex)[:,src];y=M@truth;actual=abs(t@truth)**2
        for frac in (0.,1e-4,.01,.1):
            # Norm-ball error relative to synthetic local observation. No instrument fit.
            eps=frac*np.linalg.norm(y);lo,hi,rad,rank=bound(M,t,y,eps,1.)
            assert lo-1e-26<=actual<=hi+1e-26
            # Construct perturbations of the measured observation, with truth feasible.
            for j in range(16):
                noise=rng.normal(size=2)+1j*rng.normal(size=2);noise*=eps/np.linalg.norm(noise)
                l,h,_,_=bound(M,t,y+noise,eps,1.);assert l-1e-26<=actual<=h+1e-26;checks+=1
            rows.append(dict(f=f,source=src,error_fraction=frac,lower=float(lo),upper=float(hi),actual=float(actual),relative_width=float((hi-lo)/actual)))
    # Covariance observer S_y=Yobs Yobs^H, rank-two synthetic incoherent source.
    # Fix a factor Yobs; all compatible incident factors after right-unitary
    # alignment/padding are U0+F X. Trace budget = Frobenius norm squared.
    P,F,_=fibre(M,t);Utruth=np.eye(N,dtype=complex)[:,[0,4]]/np.sqrt(2);Yobs=M@Utruth;U0=P@Yobs
    c=t@U0;k=t@F;radius=np.sqrt(1-np.linalg.norm(U0,'fro')**2);r=radius*np.linalg.norm(k)
    hi=(np.linalg.norm(c)+r)**2;lo=max(0.,np.linalg.norm(c)-r)**2
    direction=np.outer(k.conj()/np.linalg.norm(k),c/np.linalg.norm(c));Xhi=radius*direction;Xlo=-min(radius,np.linalg.norm(c)/np.linalg.norm(k))*direction
    for X,v in [(Xhi,hi),(Xlo,lo)]:
        U=U0+F@X;assert np.linalg.norm(M@U-Yobs)<1e-10 and np.linalg.norm(U,'fro')<=1+1e-10
        assert abs(np.linalg.norm(t@U)**2-v)<1e-10*max(v,1e-30);checks+=1
    actual=np.linalg.norm(t@Utruth)**2;assert lo-1e-26<=actual<=hi+1e-26
    covrows.append(dict(f=f,lower=float(lo),upper=float(hi),actual=float(actual)))
# Any bounded operator error delta and additive error eta imply effective
# observation radius eta+delta sqrt(I); timing phase error <=2 sin(pi f dt)
# for 0<=f dt<=1/2. Illustrative 1 degree channel alignment requirements.
clock=[dict(f=f,max_delay_s=1/(360*f)) for f in (.005,.05,3.915,7.83,7800.)]
print(json.dumps(dict(status='CONDITIONAL_S1_UNCERTAINTY_COVARIANCE',rows=rows,covariance=covrows,observer_ranks=ranks,perturbed_and_endpoint_checks=checks,one_degree_clock_fixture=clock,scope='Synthetic norm-ball outer bounds, exact covariance fibre endpoints in retained linear model; no empirical data, interval rounding, physical calibration or independent source attribution.'),indent=2))
