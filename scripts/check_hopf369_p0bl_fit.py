"""BL: directed-rounding bounds of the actual projected reciprocal trial.
Radial/fibre interval product, exact angular derivative inequalities.
Requires IEEE binary64 round-to-nearest basic arithmetic; transcendentals
are rational Taylor intervals from BJ, never floating sin/cos bounds.
"""
from fractions import Fraction as Q
import json,sys
from pathlib import Path
import numpy as np
from check_hopf369_p0bj_tail import I as RI, L, PI, trig, hyperbolic, poly, deriv


def down(x):return np.nextafter(x,-np.inf)
def up(x):return np.nextafter(x,np.inf)
class IV:
    def __init__(self,a,b=None):
        self.a,self.b=np.broadcast_arrays(np.asarray(a,dtype=np.float64),np.asarray(a if b is None else b,dtype=np.float64))
    @staticmethod
    def of(x):
        if isinstance(x,IV):return x
        if isinstance(x,Q):return IV(down(float(x)),up(float(x)))
        return IV(x)
    def __add__(self,x):x=IV.of(x);return IV(down(self.a+x.a),up(self.b+x.b))
    __radd__=__add__
    def __neg__(self):return IV(-self.b,-self.a)
    def __sub__(self,x):return self+-IV.of(x)
    def __rsub__(self,x):return IV.of(x)+-self
    def __mul__(self,x):
        x=IV.of(x);v=[self.a*x.a,self.a*x.b,self.b*x.a,self.b*x.b];return IV(down(np.minimum.reduce(v)),up(np.maximum.reduce(v)))
    __rmul__=__mul__
    def __truediv__(self,x):
        x=IV.of(x);assert np.all((x.a>0)|(x.b<0));return self*IV(down(1/x.b),up(1/x.a))
    def __rtruediv__(self,x):return IV.of(x)/self
    def __pow__(self,n):
        p=IV(1)
        for _ in range(n):p=p*self
        return p
    def abs(self):return IV(0,np.maximum(abs(self.a),abs(self.b)))
    def sqrt(self):assert np.all(self.a>=0);return IV(down(np.sqrt(self.a)),up(np.sqrt(self.b)))


def columns(v):return IV(np.array([down(float(z.a)) for z in v])[None,:],np.array([up(float(z.b)) for z in v])[None,:])
def horner(c,s):
    p=IV(0)
    for v in c[::-1]:p=p*s+float(v)
    return p

def bound(c,cs,N=512,M=256):
    # dyadic cells, exact binary64 endpoints; t=|x|^2, z=y/L.
    assert N&(N-1)==0 and M&(M-1)==0
    t=IV(np.arange(N)[:,None]/N,np.arange(1,N+1)[:,None]/N);delta=1-t;r=t.sqrt();h=IV.of(Q(4,5));AB=IV.of(Q(13,250)*Q(29,200))
    a=IV.of(Q(1,10));s=1-a/(a+t);ds=a/(a+t)**2
    pref=delta**2/(1+10*t);dpref=-2*delta/(1+10*t)-10*delta**2/(1+10*t)**2
    tap=1-t**2;dtap=-2*t;ca=pref*tap**2;cb=pref*tap*t**2
    dca=dpref*tap**2+2*pref*tap*dtap;dcb=dpref*tap*t**2+pref*dtap*t**2+2*pref*tap*t
    Y=[];DY=[];P=[];DP=[];bs=[];bps=[]
    pc=[[0,0,Q(1,2),-Q(3,2),Q(3,2),-Q(1,2)],[0,0,0,Q(1,2),-1,Q(1,2)]]
    omega=2*PI/L
    for k in range(M):
        z=RI(Q(k,M),Q(k+1,M));b,T=hyperbolic(z);C,S=trig(1,z);C2,S2=trig(2,z)
        Y.append([RI(1),C,S,C2,S2]);DY.append([RI(0),-omega*S,omega*C,-2*omega*S2,2*omega*C2]);P.append([L**2*poly(v,z) for v in pc]);DP.append([L*poly(deriv(v),z) for v in pc]);bs.append(b);bps.append(b*T)
    Y=[columns(v) for v in zip(*Y)];DY=[columns(v) for v in zip(*DY)];P=[columns(v) for v in zip(*P)];DP=[columns(v) for v in zip(*DP)];b=columns(bs);bp=columns(bps)
    alpha=IV(down(.998),1.);f0=1+(b-1)*alpha;fy=bp*alpha;df0=(1-b).abs()*AB
    H=[IV(1),r,r,r,t/2,t/2,t/2,t,2*t];DH=[IV(0),IV(1),IV(1),IV(1),r,r,r,2*r,4*r]
    w=IV(0);dx=IV(0);dy=IV(0)
    for i in range(9):
        a=c[:180].reshape(9,4,5)[i];d=c[180:].reshape(9,4,2)[i];astar=cs[:180].reshape(9,4,5)[i,:,0]
        def pack(a,Y,DY):
            val=IV(0);dt=IV(0);dy=IV(0)
            for k in range(a.shape[1]):
                p=horner(a[:,k],s);p1=sum((horner([a[l,k]],s)*l*s**(l-1) for l in range(1,4)),IV(0))*ds
                val=val+p*Y[k];dt=dt+p1*Y[k];dy=dy+p*DY[k]
            return val,dt,dy
        p,pt,py=pack(a,Y,DY);q,qt,qy=pack(d,P,DP)
        ps=horner(astar,s);pst=sum((horner([astar[l]],s)*l*s**(l-1) for l in range(1,4)),IV(0))*ds
        wi=ca*(f0*p+q)+cb*f0*ps
        wt=dca*(f0*p+q)+ca*(f0*pt+qt)+dcb*f0*ps+cb*f0*pst
        wy=ca*(fy*p+f0*py+qy)+cb*fy*ps
        wf=ca*p+cb*ps
        w=w+H[i]*wi.abs();dx=dx+H[i]*wt.abs()*h*delta*r+wi.abs()*h*delta*DH[i]/2+H[i]*wf.abs()*df0;dy=dy+H[i]*wy.abs()
    out=[float(np.max(v.b)) for v in (w,dx,dy)];assert np.all(np.isfinite(out));print('directed full-ball interval majorants |w|, |grad_gamma w|, |w_y|',out,'cells',N*M,flush=True)
    return out

if __name__=='__main__':
    c=np.array(json.loads(Path(sys.argv[1]).read_text().split('COEFFICIENTS ')[-1]));cs=np.array(json.loads(Path(sys.argv[2]).read_text()));assert len(c)==len(cs)==252
    vals=bound(c,cs);assert all(Q(float(v))<b for v,b in zip(vals,[Q(2602,10**6),Q(14251,10**6),Q(12675,10**6)]))
