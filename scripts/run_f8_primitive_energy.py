"""Full-clock conditional primitive/memory residual and source observation interval.
Independent checkpoint; literal original stage subset; outward binary64 assumptions.
"""
import argparse,hashlib,json,math,os,time
from pathlib import Path
from functools import lru_cache
from fractions import Fraction as Q
import numpy as np
from scipy.integrate import quad
import check_f8_vector_interval as vi
from check_f8_local_dual_weld import I,bump,window_coordinate,source_box
from check_f8_combined_residual import clock_box
from check_f8_sharp_energy import rate
from run_f8_primitive_adjoint import step,H,END,NY,DY,N,T0,clock,digest
from run_f8_bidirectional_low_dual import K,KD,jets

BS=8

def cube(a):return a.square()*a

def positive(a):return vi.V(np.maximum(0,a.l),np.maximum(0,a.h))

def upper(a):return vi.V(np.maximum(0,a.h))

def tile(x):return vi.V(np.tile(x.l,2),np.tile(x.h,2))

@lru_cache(4)
def block(i):
    t0=i*Q(H);t1=min(i+BS,END)*Q(H)
    b0,b1=clock(T0+float(t0))[0],clock(T0+float(t1))[0]
    box=clock_box(t0,t1,Q(math.floor(b1*10**10)-2,10**10),Q(math.ceil(b0*10**10)+2,10**10));b,v,s,a=[vi.V.rational(*p) for p in box];u=-v
    w=1/cube(b);sw=w.sqrt();beta=(1+b.square()).sqrt();b3=cube(b);d=a-3*u.square()/b
    chi=vi.from_i(bump(window_coordinate(t0,t1),1)[0]);J=-b.square()/beta
    A2=-b.square()*beta.square()*chi*vi.V([.25,.25,.5,.5]);A1=-b.square()*(J+vi.V([0,0,2,2])*beta)*chi*vi.V([.25,.25,.5,.5]);A0=b.square()*chi*vi.V([-.25,-.25,.5,.5])
    src=[source_box(box,t0,t1,n) for n in (1,2)];g=tile(vi.stack([vi.from_i(x[0]) for x in src]));gt=tile(vi.stack([vi.from_i(x[1]) for x in src]));active=t0<Q(13,200)
    # Signed matrix entries, then Gershgorin on the bulk-energy norm and two memory magnitudes.
    den=1+u.square();alpha=2*u/den;eta=s/den;delta=alpha/4;c=3*u/(2*b);ell0=eta+d/den;ell1=u*KD/den
    c00=c+u*d/den+ell0.square()/(2*alpha);c11=c+ell1.square()/(2*alpha);c01=(-s*KD+u.square()*KD/den)/2+ell0*ell1/(2*alpha)
    C0=(3/(b*KD.square())+1/(KD*s.sqrt())).sqrt();off=u*KD.square()*C0/2;gam=vi.rat(rate(box,True))
    # Entrywise nonnegative off diagonal majorant of production form. Row sums bound its top eigenvalue.
    gamma=vi.V(np.maximum.reduce([(gam+off).h,(c00+off+vi.V(c01.mag())).h,(c11+vi.V(c01.mag())).h,np.zeros(4)]))
    cg=eta.square()/alpha;h1=sw*(gt+3*u*g/b);h2=-u*g*KD*sw
    return b,u,s,a,w,sw,b3,d,A2,A1,A0,den,alpha,eta,delta,gamma,cg,h1,h2,g,gt,active

def linear(J,K):
    a=vi.V(J);b=vi.V(K)
    return vi.stack([a,(2*a+b)/3,(a+2*b)/3,b])

def residual(X,Y,J,K,i,C):
    b,u,s,a,w,sw,b3,d,A2,A1,A0,den,alpha,eta,delta,gamma,cg,h1,h2,g,gt,active=C
    # Reverse clock coordinate: left=at i+1, right=at i. Jets are literal reconstruction data.
    L=jets(X,-clock(T0+(i+1)*H)[1],DY);R=jets(Y,-clock(T0+i*H)[1],DY)
    c,ct,cy,ctt,cty,cyy=vi.derivatives(L,R,H,DY)
    idx=np.arange(NY-1)[:,None];z=b+vi.V(idx,idx+1)*DY;weight=1/cube(z)
    r=(ctt-2*u*cty-s*cyy+(3/z-a)*cy+KD.square()*c).hull((0,1));norm=(vi.V(0,r.mag()).square()*weight*DY).sum(0)
    vol=upper(positive(norm).sqrt()*H)
    wall=lambda p:p[:,0,0,:]
    W,N0,F0=wall(ct),wall(cy),wall(c);F1=-W+u*N0
    mem=linear(J,K);j0,j1=mem[:,0,:],mem[:,1,:];dj=(vi.V(K)-vi.V(J))/H
    G=(b3*(j0+s*A2)-den*N0+u*W).hull(0);eg=upper(sw*vi.V(G.mag()))
    r0=(dj[0]-(-s*(j1-A1)+2*u*a*A2+d*w*F1+u*KD.square()*w*F0)).hull(0)
    r1=(dj[1]-(KD.square()*A0+u*KD.square()*w*F1)).hull(0)
    force=upper(vol+H/sw*(vi.V(r0.mag())+vi.V(r1.mag())/KD)+H*u/den*(vi.V(d.mag())+u*KD)*eg)
    wallQ=upper(cg*eg.square()*H)
    obs=(-w*(gt+3*u*g/b)*F1+u*g*j1).hull(0)*H
    return vol,eg,force,wallQ,obs,vi.V(r0.mag()),vi.V(r1.mag())

def advance(B,force,wallQ,gamma):
    B=vi.V(B);den=1-vi.V(H)*gamma;assert np.all(den.l>0)
    return upper((positive(B.square()+2*wallQ).sqrt()+force)/den).h

def seal(meta,i,X,J,A):return hashlib.sha256((meta+'|'+str(i)+'|'+digest(X)+'|'+digest(J)+'|'+digest(A)).encode()).hexdigest()

def run(root,budget):
    root.mkdir(parents=True,exist_ok=True);p=root/'primitive-energy.npz';normal=.1*quad(lambda u:math.exp(1-1/(1-u*u)),-1,1,epsabs=1e-13)[0]
    files=['run_f8_primitive_energy.py','run_f8_primitive_adjoint.py','run_f8_bidirectional_low_dual.py','run_f8_accumulated_interval.py','run_f8_streaming_residual.py','run_f8_common_modal_box.py','f8_fused_step.py','ksw668_f8_tt_multipole.py','check_f8_vector_interval.py','check_f8_local_dual_weld.py','check_f8_combined_residual.py','check_f8_sharp_energy.py'];base=Path(__file__).parent
    meta=json.dumps(dict(h=H,end=END,dy=DY,block=BS,norm=normal,modules={x:hashlib.sha256((base/x).read_bytes()).hexdigest() for x in files}),sort_keys=True)
    # ledger rows: B; vol; integral eg; integral memory r0,r1; max gamma;
    # source p dissipation budget; source CS coefficient; source remaining radius;
    # signed reconstructed observation lower, upper.
    if p.exists():
        with np.load(p,allow_pickle=False) as f:
            i=int(f['cursor']);X=f['X'];J=f['J'];A=f['ledger'];assert f['meta'].item()==meta and f['seal'].item()==seal(meta,i,X,J,A)
    else:i=END;X=np.zeros((6,NY,N));J=np.zeros((2,N));A=np.zeros((11,N))
    initial=i;start=time.monotonic();buf=[np.empty_like(X) for _ in range(3)]
    while i>0:
        C=block((i-1)//BS*BS);b,u,s,a,w,sw,b3,d,A2,A1,A0,den,alpha,eta,delta,gamma,cg,h1,h2,g,gt,active=C
        Y,K=step(X,J,T0+i*H,normal,buf);vol,eg,force,wallQ,obs,r0,r1=residual(X,Y,J,K,i-1,C)
        incoming=A[0].copy();B=advance(incoming,force,wallQ,gamma);A[0]=B
        for j,q in ((1,vol),(2,eg*H),(3,r0*H),(4,r1*H)):A[j]=upper(vi.V(A[j])+q).h
        A[5]=np.maximum(A[5],gamma.h)
        if active:
            # Telescope source-support dissipation; charge incoming energy ONCE.
            if (i//BS)*BS*Q(H)>=Q(13,200) and (i-1)//BS*BS*Q(H)<Q(13,200):A[6]=upper(vi.V(A[6])+vi.V(incoming).square()/2).h
            A[6]=upper(vi.V(A[6])+gamma*H*vi.V(B).square()+vi.V(B)*force+wallQ).h
            A[7]=upper(vi.V(A[7])+H*(h1/den).square()/delta).h
            A[8]=upper(vi.V(A[8])+H*(vi.V(h1.mag())*u/den*(vi.V(B)+eg)+vi.V(h2.mag())*vi.V(B))).h
            o=vi.V(A[9],A[10])+obs;A[9],A[10]=o.l,o.h
        X,buf[2]=Y,X;J=K;i-=1;assert np.isfinite(A).all()
        if i%128==0 or i==0 or time.monotonic()-start>=budget:
            sig=seal(meta,i,X,J,A);tmp=p.with_suffix('.tmp')
            with tmp.open('wb') as f:np.savez(f,meta=meta,cursor=i,X=X,J=J,ledger=A,seal=sig);f.flush();os.fsync(f.fileno())
            os.replace(tmp,p)
            with np.load(p,allow_pickle=False) as f:assert f['seal'].item()==seal(f['meta'].item(),int(f['cursor']),f['X'],f['J'],f['ledger'])==sig
            if time.monotonic()-start>=budget:break
    radius=upper(positive(vi.V(A[6])*vi.V(A[7])).sqrt()+vi.V(A[8])).h
    return dict(initial=initial,cursor=i,seconds=time.monotonic()-start,state_sha=digest(X),memory_sha=digest(J),ledger=A.tolist(),radius=radius.tolist(),meta=json.loads(meta),scope='conditional full-clock primitive scalar residual and source contraction; no TT or omitted-tail acceptance')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('root',type=Path);p.add_argument('--budget',type=float,default=20);a=p.parse_args();assert 0<a.budget<=75;print(json.dumps(run(a.root,a.budget)),flush=True)
