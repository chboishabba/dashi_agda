"""Independent forced covector evolution on original BR256 metric snapshots.
Zero-extension restricted grid, not physical causal boundary. Exact discrete
quadratic storage ledger; forcing uses discrete reduced Ricci defect.
"""
import numpy as np
from scipy.sparse.linalg import LinearOperator, gmres
from check_hopf369_br256_spatial import operators, diff


def geometry(g,v,a,dx):
    I=np.linalg.inv(g); den=np.sqrt(-np.linalg.det(g))
    f=np.zeros(g.shape[:-2]+(5,5,5)); f[...,0,:,:]=v
    for i in range(1,4): f[...,i,:,:]=diff(g,dx,i-1)
    h=np.zeros(g.shape[:-2]+(5,5,5,5));h[...,0,0,:,:]=a
    for i in range(1,4):
        h[...,0,i,:,:]=h[...,i,0,:,:]=diff(v,dx,i-1)
        for j in range(1,4):h[...,i,j,:,:]=diff(f[...,j,:,:],dx,i-1)
    h=(h+h.swapaxes(-4,-3))/2
    L=(f.swapaxes(-3,-2)+np.moveaxis(f,-3,-1)-f)/2
    DL=(h.swapaxes(-3,-2)+np.moveaxis(h,-3,-1)-h)/2
    DI=-np.einsum('...ar,...krs,...sb->...kab',I,f,I)
    G=np.einsum('...ae,...ebc->...abc',I,L)
    DG=np.einsum('...kae,...ebc->...kabc',DI,L)+np.einsum('...ae,...kebc->...kabc',I,DL)
    C=np.einsum('...bc,...abc->...a',I,L)
    DC=np.einsum('...kbc,...abc->...ka',DI,L)+np.einsum('...bc,...kabc->...ka',I,DL)
    R=np.einsum('...aamn->...mn',DG)-np.einsum('...nama->...mn',DG)+np.einsum('...aac,...cmn->...mn',G,G)-np.einsum('...anc,...cma->...mn',G,G)
    U=DC-np.einsum('...amn,...a->...mn',G,C); E=R-(U+U.swapaxes(-1,-2))/2
    # lower-order terms in density-weighted covector wave
    T=-2*den[...,None,None,None]*np.einsum('...ab,...cam->...bmc',I,G)
    Z=den[...,None,None]*(-np.einsum('...ab,...acbm->...mc',I,DG)+np.einsum('...ab,...dab,...cdm->...mc',I,G,G)+np.einsum('...ab,...dam,...cbd->...mc',I,G,G)+R@I)
    return dict(A=-den*I[...,0,0],B=den[...,None]*I[...,0,1:4],D=den[...,None,None]*I[...,1:4,1:4],I=I,G=G,E=E,C=C,DC=DC,T=T,Z=Z,den=den)


def run(n=11,steps=8):
    init,acc=operators(4);g,v,dx=init(n);dt=.06/steps
    def rhs(g,v):
        a=acc(g,v,dx);w=v.copy()
        for i in range(3):
            for j in (0,-1):
                p=[slice(None)]*3;p[i]=j;a[tuple(p)]=0;w[tuple(p)]=0
        return w,a
    hist=[]
    for k in range(steps+1):
        u,a=rhs(g,v);hist.append(geometry(g,u,a,dx))
        if k==steps:break
        w,b=rhs(g+dt*u/2,v+dt*a/2);x,c=rhs(g+dt*w/2,v+dt*b/2);y,e=rhs(g+dt*x,v+dt*c)
        g+=dt*(u+2*w+2*x+y)/6;v+=dt*(a+2*b+2*c+e)/6
    sl=(slice(2,-2),)*3; shape=hist[0]['C'][sl].shape; size=np.prod(shape);dv=dx**3
    # Restricted skew centered derivative: zero extension, no boundary flux.
    def der(q,i):
        pads=[(0,0)]*q.ndim;pads[i]=(2,2);a=np.moveaxis(np.pad(q,pads),i,0)
        return np.moveaxis((a[:-4]-8*a[1:-3]+8*a[3:-1]-a[4:])/(12*dx),0,i)
    def grad(q):return np.stack([der(q,i) for i in range(3)],axis=-2)
    def div(q):return sum(der(q[...,i,:],i) for i in range(3))
    rng=np.random.default_rng(369);x=rng.normal(size=shape);y=rng.normal(size=shape)
    assert max(abs(np.sum(x*der(y,i)+der(x,i)*y)) for i in range(3))<1e-10
    def coeff(h):return tuple(h[k][sl] for k in ('A','B','D'))
    def velocity(q,p,c):
        A,B,D=c;return (p+np.einsum('...i,...im->...m',B,grad(q)))/A[...,None]
    def energy(q,p,c):
        A,B,D=c;w=grad(q);u=velocity(q,p,c)
        return dv*.5*np.sum(A[...,None]*u*u+np.einsum('...ij,...im,...jm->...m',D,w,w)+q*q)
    q=hist[0]['C'][sl].copy();A,B,D=coeff(hist[0]);p=A[...,None]*hist[0]['DC'][sl][...,0,:]-np.einsum('...i,...im->...m',B,grad(q))
    worst=0.;total=0.;maxforce=0.;margin=1e10;initial=energy(q,p,coeff(hist[0]));
    for k,(h0,h1) in enumerate(zip(hist,hist[1:])):
        h={key:(h0[key]+h1[key])/2 for key in h0};c0=coeff(h0);c1=coeff(h1);cm=coeff(h)
        A,B,D=cm;margin=min(margin,A.min(),np.linalg.eigvalsh(D).min());assert margin>0
        E=h['E'];DE=np.zeros(E.shape[:-2]+(5,5,5));DE[...,0,:,:]=(h1['E']-h0['E'])/dt
        for i in range(1,4):DE[...,i,:,:]=diff(E,dx,i-1)
        G=h['G'];CE=DE-np.einsum('...aki,...aj->...kij',G,E)-np.einsum('...akj,...ia->...kij',G,E)
        F=(-2*np.einsum('...ki,...kij->...j',h['I'],CE)+np.einsum('...ij,...kij->...k',h['I'],CE))[sl]*h['den'][sl][...,None]
        maxforce=max(maxforce,np.max(abs(F)))
        T=h['T'][sl];Z=h['Z'][sl]
        def op(q,p):
            u=velocity(q,p,cm);w=grad(q);j=B[..., :,None]*u[...,None,:]+np.einsum('...ij,...jm->...im',D,w)
            lower=np.einsum('...mc,...c->...m',T[...,0,:,:],u)+np.einsum('...imc,...ic->...m',T[...,1:4,:,:],w)+np.einsum('...mc,...c->...m',Z,q)
            return u,div(j)+lower,lower
        def pack(q,p):return np.r_[q.ravel(),p.ravel()]
        def unpack(z):return z[:size].reshape(shape),z[size:].reshape(shape)
        def lin(z):return z-dt/2*pack(*op(*unpack(z))[:2])
        old=pack(q,p);b=old+dt/2*pack(*op(q,p)[:2])-dt*pack(np.zeros(shape),F)
        new,info=gmres(LinearOperator((2*size,2*size),matvec=lin),b,rtol=1e-12,atol=1e-13);assert info==0
        q1,p1=unpack(new);qm=(q+q1)/2;pm=(p+p1)/2;u,_,lower=op(qm,pm)
        work=dt*dv*np.sum(u*(qm+lower-F));metric=energy(q1,p1,c1)-energy(q1,p1,cm)+energy(q,p,cm)-energy(q,p,c0)
        err=energy(q1,p1,c1)-energy(q,p,c0)-metric-work
        worst=max(worst,abs(err));total+=metric+work;assert worst<1e-9
        q,p=q1,p1
    final=energy(q,p,coeff(hist[-1]));assert abs(final-initial-total)<1e-8
    target=hist[-1]['C'][sl];print('BR257-259',n,steps,'energy initial/final',initial,final,'work',total,'ledger',worst,'force',maxforce,'margin',margin,'gauge mismatch',np.max(abs(q-target)),flush=True)


if __name__=='__main__':run()
