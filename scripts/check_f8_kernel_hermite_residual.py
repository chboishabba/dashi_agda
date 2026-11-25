"""Bicubic characteristic kernel residual, signed rational-potential numerator.
Targeted whole endpoint rectangle; IEEE outward arithmetic, no Volterra enclosure.
"""
import json,math,sys,time
from fractions import Fraction as Q
import numpy as np
from check_f8_global_wall_kernel import Fbox,grid,derivatives,certify

D=lambda x:np.nextafter(x,-np.inf);U=lambda x:np.nextafter(x,np.inf)
class I:
    def __init__(self,l,h=None):self.l=np.asarray(l,dtype=float);self.h=self.l if h is None else np.asarray(h,dtype=float)
    def __getitem__(a,i):return I(a.l[i],a.h[i])
    def __add__(a,b):
        b=iv(b);return I(D(a.l+b.l),U(a.h+b.h))
    __radd__=__add__
    def __neg__(a):return I(-a.h,-a.l)
    def __sub__(a,b):return a+-iv(b)
    def __rsub__(a,b):return iv(b)+-a
    def __mul__(a,b):
        b=iv(b);p=a.l*b.l;q=a.l*b.h;r=a.h*b.l;s=a.h*b.h;return I(D(np.minimum(np.minimum(p,q),np.minimum(r,s))),U(np.maximum(np.maximum(p,q),np.maximum(r,s))))
    __rmul__=__mul__
    def __truediv__(a,b):
        b=iv(b);assert np.all(b.l>0);return a*I(D(1/b.h),U(1/b.l))
    def mag(a):return np.maximum(abs(a.l),abs(a.h))
def iv(x):return x if isinstance(x,I) else I(x)
def rat(x):return I(D(float(x)),U(float(x)))
def stack(a,axis=0):return I(np.stack([x.l for x in a],axis),np.stack([x.h for x in a],axis))
def axis(a,i):return I(np.moveaxis(a.l,i,0),np.moveaxis(a.h,i,0))
def elev(a,n):
    return stack([a[0]]+[(a[i-1]*i+a[i]*(n+1-i))/(n+1) for i in range(1,n+1)]+[a[n]])
def diff(a,i,h):
    b=axis(a,i);n=len(b.l)-1;return axis((b[1:]-b[:-1])*n/h,i)
def elevate(a,i):
    b=axis(a,i);return axis(elev(b,len(b.l)-1),i)

def hermite(R,RA,RB,RAB,h):
    H=rat(Q(h)/3);r,ra,rb,rab=[I(a) for a in (R,RA,RB,RAB)]
    val=[r[:-1],r[:-1]+H*ra[:-1],r[1:]-H*ra[1:],r[1:]];db=[rb[:-1],rb[:-1]+H*rab[:-1],rb[1:]-H*rab[1:],rb[1:]]
    return stack([stack([a[:,:-1],a[:,:-1]+H*b[:,:-1],a[:,1:]-H*b[:,1:],a[:,1:]]) for a,b in zip(val,db)])

def mulz(a,z,h):
    # z=z0+h*x/2-h*y/2. Product with affine tensor Bernstein controls.
    n,m=np.array(a.l.shape[:2])-1;rows=[]
    zz=[[z,z-h/2],[z+h/2,z]]
    for i in range(n+2):
        row=[]
        for j in range(m+2):
            q=I(0)
            for di in (0,1):
                for dj in (0,1):
                    p=i-di;r=j-dj
                    if 0<=p<=n and 0<=r<=m:
                        w=Q((i if di else n+1-i)*(j if dj else m+1-j),(n+1)*(m+1))
                        q=q+rat(w)*zz[di][dj]*a[p,r]
            row.append(q)
        rows.append(stack(row))
    return stack(rows)

def pi_box():
    def atan(q):
        v=sum((-1)**j*Q(1,q)**(2*j+1)/(2*j+1) for j in range(32));return v,v+Q(1,q)**65/65
    l,h=atan(5);a,b=atan(239);return 16*l-4*b,16*h-4*a

def prefix(q):
    q=q.copy()
    for i in range(1,len(q)):q[i]=U(q[i]+q[i-1])
    for j in range(1,q.shape[1]):q[:,j]=U(q[:,j]+q[:,j-1])
    return q

def run(mode,source,target,h,rich=False):
    st=time.monotonic();a,c=Fbox(source);l,r=Fbox(target);lo=min(a-r,l-c);hi=max(c-l,r-a);T=I(D(float(max(a-r,l-c))),U(float(hi)));xi=rat(source);dz=rat(target-source);A=T+dz;B=T-dz;na=int(np.floor(A.h/h))+1;nb=int(np.floor(B.h/h))+1
    k=mode*np.pi/3.012;pl,ph=pi_box();K=I(D(float(mode*pl/Q('3.012'))),U(float(mode*ph/Q('3.012'))));K2=K*K;cut=rat(Q(1,13));R=grid(float(source),k,h,na,nb);RA,RB=derivatives(R,float(source),k,h);z=np.maximum(1/13,float(source)+(np.arange(na+1)[:,None]-np.arange(nb+1)[None,:])*h/2);RAB=-(k*k+3.75/z**2)*R/4
    if rich:
        fine=grid(float(source),k,h/2,2*na,2*nb);fa,fb=derivatives(fine,float(source),k,h/2)
        R,RA,RB=[(4*f[::2,::2]-r)/3 for f,r in ((fine,R),(fa,RA),(fb,RB))]
        RAB=-(k*k+3.75/z**2)*R/4
        del fine,fa,fb
    res=np.empty((na,nb));vmax=np.empty_like(res);last=None
    for start in range(0,na,12):
        stop=min(na,start+12);p=hermite(R[start:stop+1],RA[start:stop+1],RB[start:stop+1],RAB[start:stop+1],h);ab=elevate(elevate(diff(diff(p,0,h),1,h),0),1);q=4*ab+K2*p
        z0=xi+I((np.arange(start,stop)[:,None]-np.arange(nb)[None,:])*h/2);zl=(z0-h/2).l;zh=(z0+h/2).h
        num=mulz(mulz(q,z0,h),z0,h)+rat(Q(15,4))*elevate(elevate(elevate(elevate(p,0),0),1),1)
        # Two potential branches. On crossing cells both are charged; numerator
        # may be evaluated outside the branch, but denominator >= cutoff^2.
        den=np.maximum(cut.l,zl);above=U(np.max(num.mag(),axis=(0,1))/D(den*den));below=np.max((q+rat(Q(15*13**2,4))*p).mag(),axis=(0,1));res[start:stop]=np.maximum(np.where(zh>=cut.l,above,0),np.where(zl<=cut.h,below,0));vmax[start:stop]=U(K2.h+U(3.75/D(den*den)))
        if stop==na:last=p[:,:, -1,-1]
    # Positive-wave energy bound on each characteristic prefix. Each cell area
    # is dyadic. Prefix envelope gives the derivative-error integral locally.
    q=prefix(U(U(res*res)*h*h));tt=(np.arange(1,na+1)[:,None]+np.arange(1,nb+1)[None,:])*h/2;err=U(tt*U(np.sqrt(U(q/2))));g=U(res+U(vmax*err));ea=0.;eb=0.
    for x in g[-1,:]:ea=U(ea+U(x*h/4))
    for x in g[:,-1]:eb=U(eb+U(x*h/4))
    # Actual endpoint box lies in last cell (strict guard). Use full Bernstein hull.
    assert A.l>=(na-1)*h and B.l>=(nb-1)*h
    dA=diff(last,0,h);dB=diff(last,1,h);e=err[-1,-1];errD=U(U(ea+eb)/2)
    hull=lambda a:[float(np.min(a.l)),float(np.max(a.h))]
    val=[D(np.min(last.l)/2-U(e/2)),U(np.max(last.h)/2+U(e/2))];dt=[D(D(np.min(dA.l)+np.min(dB.l))/2-errD),U(U(np.max(dA.h)+np.max(dB.h))/2+errD)];dz=[D(D(np.min(dA.l)-np.max(dB.h))/2-errD),U(U(np.max(dA.h)-np.min(dB.l))/2+errD)]
    old,oldmax=certify(R,xi.l,xi.h,mode,h,np.array([float((A.l+A.h)/2)]),np.array([float((B.l+B.h)/2)]),np.array([max(float(A.h-A.l),float(B.h-B.l))+1e-13]))
    return dict(mode=mode,source=str(source),target=str(target),h=h,richardson=rich,cells=na*nb,seconds=time.monotonic()-st,max_residual=float(res.max()),old_max_residual=oldmax,value_error=float(e/2),derivative_error=float(errD),bounds=[list(map(float,x)) for x in (val,dt,dz)],bilinear_same_nodes_bounds=old.tolist(),scope='conditional whole endpoint characteristic rectangle; no continuous wall-pair matrix')
if __name__=='__main__':print(json.dumps(run(int(sys.argv[1]),Q(sys.argv[2]),Q(sys.argv[3]),2.**-int(sys.argv[4]),'--rich' in sys.argv),indent=2),flush=True)
