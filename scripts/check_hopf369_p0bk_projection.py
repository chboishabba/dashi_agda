"""BK: project the first admissible tail onto the AK normal ground state.
Quadrature approximates the projection coefficient; exact normal shape is retained.
"""
from check_hopf369_p0bk import *


def projected_coefficients(c,n=64):
    z,wt=np.polynomial.legendre.leggauss(n);y=L*(z+1)/2
    b=np.cosh(y-L/2)/1.25
    Y=np.stack([np.ones(n),np.cos(2*np.pi*y/L),np.sin(2*np.pi*y/L),np.cos(4*np.pi*y/L),np.sin(4*np.pi*y/L)],axis=1)
    P=np.stack([y*y*(1-y/L)**3/2,(L-y)**2*(y/L)**3/2],axis=1)
    # Normal eigenproblem has measure b dy; projection onto b uses b^3 on q/b.
    denom=wt@(b**3);a=(wt*b**3)@Y/denom;d=(wt*b**2)@P/denom
    out=np.zeros_like(c);out[:180].reshape(9,4,5)[:,:,0]=c[:180].reshape(9,4,5)@a+c[180:].reshape(9,4,2)@d
    return out


def trial(X,q,qstar,m):
    # w=(1-r^2)[q+(r^m)(qstar-q)], r=|x|^2, q and qstar are actual w jets.
    # At delta=0, w/delta^3=2 b times the ground-state angular amplitude.
    blend=q if m==0 else qstar-taper(X,qstar-q,m)
    return taper(X,blend,2)


def seam(B,v,N):
    r,g,I,G,Ric=map(np.asarray,Ebatch(*B,v));K=-G[:,3,:3,:3]/np.sqrt(I[:,3,3,None,None]);H=g[:N,:3,:3];Hi=np.linalg.inv(H);M=(K[:N]+K[N:])/2
    J2=-(Ric[:N,:3,:3]-Ric[N:,:3,:3])+J*M-J*np.trace(Hi@M,axis1=1,axis2=2)[:,None,None]*H
    mixed=Hi@J2;tf=mixed-np.trace(mixed,axis1=1,axis2=2)[:,None,None]*np.eye(3)/3
    return np.max(abs(Hi@(K[:N]-K[N:]-J*H))),np.max(abs(tf)),np.max(abs(r))


def run_projection(c):
    eps=.025;cs=projected_coefficients(c);d=np.max(abs(cs-projected_coefficients(c,128)))
    print('projection quadrature 64 vs 128 coefficient max difference',d,flush=True);assert d<1e-10
    base=sample(10,456);z=sample(7,814);x=z[:,:3]/np.linalg.norm(z[:,:3],axis=1)[:,None]
    X=np.vstack([base,*[np.c_[x*r,z[:,3]] for r in (.9,.99,.999,.9999)]]);ms=(0,2,4,8,16,32);rows={m:[] for m in ms}
    for i in range(0,len(X),128):
        xx=X[i:i+128];B,q=evaluate_points(xx,eps,c);qs=np.asarray(Qfun(j.array(xx),eps,cs));psi=weight52(xx,np.asarray(Wfun(j.array(xx),eps)))
        for m in ms:
            v=trial(xx,q,qs,m);F=np.asarray(Rbatch(*B,v));D=np.asarray(DJ(*B,v));rows[m].append(np.c_[F,F/psi[:,0],-np.sum(D*psi,axis=1)/psi[:,0],v[:,0]])
    for m in ms:
        a=np.concatenate(rows[m]);print('projection',m,'bulk RMS',np.sqrt(np.mean(a[:1024,0]**2)),'weighted bulk max',np.max(abs(a[:1024,1])),'tail layer maxima',[float(np.max(abs(a[1024+i*128:1024+(i+1)*128,1]))) for i in range(4)],'min margin',a[:,2].min(),'sample |w| max',np.max(abs(a[:,3])),flush=True)
    # Independent endpoint and signed/zero controls for all projection candidates.
    x=sample(5,987)[:,:3];Z=np.vstack([np.c_[x,np.zeros(len(x))],np.c_[x,np.full(len(x),L)]]);B,q=evaluate_points(Z,eps,c);qs=np.asarray(Qfun(j.array(Z),eps,cs));N=len(x)
    for m in ms:
        a=seam(B,trial(Z,q,qs,m),N);print('projection seam',m,a,flush=True);assert max(a[:2])<1e-8
    Z=X[:128];B,q=evaluate_points(Z,eps,c);qs=np.asarray(Qfun(j.array(Z),eps,cs));neg=c.copy();neg[:180].reshape(9,4,5)[:,:,[2,4]]*=-1;neg[180:]=c[180:].reshape(9,4,2)[:,:,::-1].ravel();R=Z.copy();R[:,3]=L-R[:,3]
    Bn,qn=evaluate_points(R,-eps,neg);qsn=np.asarray(Qfun(j.array(R),-eps,projected_coefficients(neg)))
    Bz,qz=evaluate_points(Z,0.,np.zeros_like(c))
    for m in ms:
        pos=np.asarray(Rbatch(*B,trial(Z,q,qs,m)));minus=np.asarray(Rbatch(*Bn,trial(R,qn,qsn,m)));zero=np.asarray(Rbatch(*Bz,trial(Z,qz,qz,m)))
        a=np.max(abs(pos-minus));b=np.max(abs(zero));print('projection signed/zero',m,a,b,flush=True);assert max(a,b)<1e-8


if __name__=='__main__':
    c=np.array(json.loads(Path(sys.argv[1]).read_text().split('COEFFICIENTS ')[-1]));assert len(c)==252;run_projection(c)
