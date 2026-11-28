"""F8 full-clock reduced modal interval consumer. Same original stage, separate checkpoint.
Fixed dual order 0 for modes 1,2; use 16-slab coefficient boxes by default.
No omitted-tail, W1 physical, or high-mode acceptance claim.
"""
import argparse,hashlib,json,math,os,time
from pathlib import Path
from functools import lru_cache
from fractions import Fraction as Q
import numpy as np
from numpy.polynomial.legendre import leggauss
import check_f8_vector_interval as vi
from check_f8_combined_residual import clock_box
from check_f8_local_dual_weld import I,dual,source_box,source_coeff,window_coordinate,expneg
from run_f8_streaming_residual import clock,pulse,T0,span,R,Y,eps,stage,weights,jets,digest

N=2;NY=225;DY=Y/(NY-1);NT=math.ceil(span/.0006);H=span/NT;END=NT+1
K=[I(Q(n)*Q(333,106)/Q('3.012'),Q(n)*Q(355,113)/Q('3.012')) for n in (1,2)]
KV=vi.stack([vi.from_i(k) for k in K]);KF=np.arange(1,3)*np.pi/R

def phis(poly,beta,k):
    # Geometric interval envelope for exp(-beta*k*y), per spatial cell.
    y=vi.V(np.arange(NY-1),np.arange(1,NY))*DY;Z=vi.from_i(k)*y
    p=vi.V(np.zeros(NY-1))
    for c in reversed(poly):p=p*Z+vi.from_i(c)
    base=vi.from_i(expneg(beta*k*Q(DY)));e=[vi.V(1)]
    for _ in range(NY-1):e.append(e[-1]*base)
    E=vi.V(np.array([x.l for x in e[1:]]),np.array([x.h for x in e[:-1]]))
    return p*E

@lru_cache(2)
def block(i,blocksize):
    t0=i*Q(H);t1=min(i+blocksize,END)*Q(H)
    b0,b1=clock(T0+float(t0))[0],clock(T0+float(t1))[0]
    box=clock_box(t0,t1,Q(math.floor(b1*10**10)-2,10**10),Q(math.ceil(b0*10**10)+2,10**10))
    sg=[source_box(box,t0,t1,n) for n in (1,2)];g=vi.stack([vi.from_i(x[0]) for x in sg]);gt=vi.stack([vi.from_i(x[1]) for x in sg])
    u=window_coordinate(t0,t1);rows=[]
    if u.l<1 and u.h>-1:
        for receiver in (0,1):
            d=[dual(box,u,k,0,receiver) for k in K]
            rows.append((vi.stack([phis(p,b,k) for (p,b,_,_),k in zip(d,K)],1),vi.stack([vi.from_i(p[0]) for p,_,_,_ in d]),vi.stack([vi.V.rational(z) for _,_,z,_ in d]),vi.stack([vi.from_i(q) for _,_,_,q in d])))
    return box,g,gt,rows

def module_identity(blocksize,src):
    files=['run_f8_accumulated_interval.py','check_f8_vector_interval.py','check_f8_combined_residual.py','check_f8_local_dual_weld.py','check_f8_streaming_residual.py','run_f8_streaming_residual.py','run_f8_common_modal_box.py','f8_fused_step.py','ksw668_f8_tt_multipole.py']
    base=Path(__file__).parent
    return dict(h=H,dy=DY,end=END,block=blocksize,source=digest(src),order=[0,0],modules={f:hashlib.sha256((base/f).read_bytes()).hexdigest() for f in files})

def seal(meta,cursor,X,ledger):
    return hashlib.sha256((meta+'|'+str(cursor)+'|'+digest(X)+'|'+digest(ledger)).encode()).hexdigest()

def save(path,meta,cursor,X,ledger):
    p=path.with_suffix('.tmp')
    with p.open('wb') as f:
        np.savez(f,meta=meta,cursor=cursor,X=X,ledger=ledger,seal=seal(meta,cursor,X,ledger));f.flush();os.fsync(f.fileno())
    os.replace(p,path)

def load(path,meta):
    with np.load(path,allow_pickle=False) as f:
        cursor=int(f['cursor']);X=f['X'];a=f['ledger']
        if f['meta'].item()!=meta or f['seal'].item()!=seal(meta,cursor,X,a):raise ValueError('checkpoint identity or digest')
    if not (0<=cursor<=END and X.shape==(6,NY,N) and a.shape==(2,11,N) and np.isfinite(X).all() and np.isfinite(a).all()):raise ValueError('invalid checkpoint')
    return cursor,X,a

# a[0:2, row, mode] lower/upper (nonnegative bounds duplicated as [0,upper]);
# rows 0 B, 1 int residual,2 int wall,3 int wall derivative;
# 4,5 E4 bulk/wall,6 E4 radius,7 E4 reconstructed obs;
# 8,9 SMS combined correction/radius,10 SMS reconstructed obs.
def accum(a,j,x):
    old=vi.V(a[0,j],a[1,j]);new=old+x;a[0,j]=new.l;a[1,j]=new.h

def run(path,blocksize,budget):
    x,w=leggauss(512);r=eps*(1+x)/2;src=math.sqrt(2/R)*eps**4*(np.sin(KF[:,None]*r)@(w*r*np.exp(1-1/(1-(r/eps)**2))*eps/2))
    assert all(source_coeff(n).contains(Q(src[n-1])) for n in (1,2))
    meta=json.dumps(module_identity(blocksize,src),sort_keys=True);path.parent.mkdir(parents=True,exist_ok=True)
    if path.exists():i,X,a=load(path,meta)
    else:i,X,a=0,np.zeros((6,NY,N)),np.zeros((2,11,N))
    initial=i;out,A,D=[np.empty_like(X) for _ in range(3)];start=time.monotonic()
    while i<END:
        T=T0+i*H;box,g,gt,rows=block(i//blocksize*blocksize,blocksize)
        left=jets(X,clock(T)[1],DY)
        for q,(inp,dst,t) in enumerate(((X,A,T),(A,D,T+H),(D,out,T+H/2))):
            b,v,s,acc=clock(t);z,lo,hi,*_=weights(b,DY,NY);stage(inp,X,dst,H,q,DY,v,pulse(t)[0],src,KF*KF,z,lo,hi)
        right=jets(out,clock(T+H)[1],DY)
        R0,G,GT,r,gerr,w,wall=vi.primal(left,right,H,DY,KV,box,g,gt)
        B=vi.energy(a[1,0],H,KV,box,R0,G,GT);a[0,0]=0;a[1,0]=B
        for j,v in enumerate((R0,G,GT),1):accum(a,j,vi.V(0,v))
        for receiver,(p,p0,d,q) in enumerate(rows):
            bulk=(r*w*p*DY*H).sum(0);b=vi.V.rational(*box[0]);lower=gerr*p0*H/(b.square()*b)
            rad=vi.V(0,B)*H*d/vi.V(KV.l);obs=q*wall*H
            if receiver==0:
                for j,v in zip((4,5,6,7),(bulk,lower,rad,obs)):accum(a,j,v)
            else:
                for j,v in zip((8,9,10),(bulk+lower,rad,obs)):accum(a,j,v)
        assert np.isfinite(a).all();X,out=out,X;i+=1
        if i%32==0 or i==END or time.monotonic()-start>=budget:
            save(path,meta,i,X,a);j,Z,aa=load(path,meta);assert j==i and np.array_equal(Z,X) and np.array_equal(aa,a)
            if time.monotonic()-start>=budget:break
    return dict(initial=initial,cursor=i,end=END,seconds=time.monotonic()-start,ledger=a.tolist(),state_sha=digest(X),identity=json.loads(meta),scope='full-clock reduced two-mode interval consumer; conditional on IEEE binary64 basic operations and original energy/reference theorem, no omitted tail or full tensor claim')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('path',type=Path);p.add_argument('--block',type=int,default=16);p.add_argument('--budget',type=float,default=30);a=p.parse_args();assert 0<a.budget<=75 and 1<=a.block<=64;print(json.dumps(run(a.path,a.block,a.budget)),flush=True)
