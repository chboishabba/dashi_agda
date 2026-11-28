"""Original weighted4 modal CFL: uniform analytic envelope and sampled stage norms."""
import json, math
from fractions import Fraction as F
import numpy as np
from scipy import sparse as sp
from scipy.linalg import eigh_tridiagonal
from scipy.optimize import brentq
from scipy.sparse.linalg import eigsh


def clock(t):return math.asinh(t)-math.sqrt(1+t*t)/t


def radial(d,n,h):
    j=np.arange(1,n,dtype=float);hi=j+.5;lo=j-.5;den=hi**d-lo**d
    p=np.r_[2*d,d*hi**(d-1)/den];m=np.r_[0.,d*lo**(d-1)/den]
    return (p+m)/h**2,-np.sqrt(p[:-1]*m[1:])/h**2


def radial_upper(d,n,h):
    p=[];m=[]
    for j in range(n):
        if j==0:p.append(F(2*d));m.append(F(0));continue
        a,b=F(2*j-1,2),F(2*j+1,2);den=b**d-a**d
        p.append(d*b**(d-1)/den);m.append(d*a**(d-1)/den)
    scale=10**9
    def up(x):return F(math.isqrt(x.numerator*scale**2//x.denominator)+1,scale)
    off=[F(0)]+[up(p[j]*m[j+1]) for j in range(n-1)]+[F(0)]
    return max(p[j]+m[j]+off[j]+off[j+1] for j in range(n))/F(str(h))**2


def normal(t,dy,n,route):
    v=-1/math.sqrt(1+t*t);a,c=(1+v)/2,(1-v)/2
    sa,sc=math.sqrt(a),math.sqrt(c);z=1/t+dy*np.arange(n)
    H=np.ones(n);H[[0,-1]]=.5;B=H*z**-3
    D=sp.diags([-np.ones(n-1)/(2*dy),np.zeros(n),np.ones(n-1)/(2*dy)],[-1,0,1],format='lil')
    D[0,0]=-1/dy;D[0,1]=1/dy;D[-1,-2]=-1/dy;D[-1,-1]=1/dy;D=D.tocsr()
    sim=lambda A,w:sp.diags(np.sqrt(w))@A@sp.diags(1/np.sqrt(w))
    D0=sim(D,H);Z=sp.diags(1.5/z);C=D0+Z-sim(D,B)
    I=sp.eye(n,format='csr');O=sp.csr_matrix((n,n));wall=sp.diags(np.r_[1.,np.zeros(n-1)]);top=sp.diags(np.r_[np.zeros(n-1),1.])
    K=sp.bmat([[O,sa*I,sc*I],[-sa*I,O,O],[-sc*I,O,O]],format='csr')
    N=sp.bmat([[O,O,O],[O,(1+v)*(D0-2*top/dy)+v*Z,(sa/sc)*Z],[O,-(sc/sa)*Z+2*math.sqrt(1-v*v)*wall/dy,(v-1)*(D0+2*wall/dy)+v*Z]],format='csr')
    if route=='paired':
        J=sp.bmat([[sa*I,sc*I],[sc*I,-sa*I]],format='csr')
        N+=sp.block_diag((O,J.T@sp.bmat([[O,C.T],[-C,O]],format='csr')@J*math.sqrt(1-v*v)),format='csr')
    elif route!='ledger':raise ValueError(route)
    return K,N,np.concatenate([np.sqrt(B),np.sqrt(a*B),np.sqrt(c*B)])


def envelope(dr,dy,nr,route):
    # Uniform on t in [1,13]; exact rational bounds, see roadmap.
    if route not in ('paired','ledger') or F(str(dy))*13>F(3,5):raise ValueError('outside envelope')
    lam=max(radial_upper(d,nr,dr) for d in (3,7,11))
    scale=10**6;omega=F(math.isqrt(lam.numerator*scale**2//lam.denominator)+1,scale)
    K=omega+F(81,16)/F(str(dy))+24+F(3,2)+(91 if route=='paired' else 0)
    return lam,K,F(9,10)/K


def norm(A):
    gram=A.T@A
    return math.sqrt(max(0.,float(eigsh(gram,k=1,which='LA',tol=1e-6,return_eigenvectors=False,v0=np.linspace(1,2,A.shape[0]))[0])))


def moving(t,dt,dy,n,omega,route):
    T=clock(t);times=[t,brentq(lambda u:clock(u)-T-dt,1,14),brentq(lambda u:clock(u)-T-dt/2,1,14)]
    data=[normal(u,dy,n,route) for u in times];h0=data[0][2];maps=[]
    for K,N,hj in data:
        Q=sp.diags(h0/hj);Qi=sp.diags(hj/h0)
        maps.append(sp.eye(len(h0),format='csr')+dt*(Q@(omega*K+N)@Qi))
    I=sp.eye(len(h0),format='csr');A,B,C=maps
    E=(I+2*C@(.75*I+.25*B@A))/3
    return norm(sp.diags(data[1][2]/h0)@E)


def run():
    records=[]
    for dr,dy,ny,dt in ((.008,.012,169,.0018),(.006,.009,225,.0012),(.008,.012,337,.0018),(.006,.009,449,.0012)):
        nr=math.ceil(3.01/dr);rad=[]
        for d in (3,7,11):
            a,b=radial(d,nr,dr);x=eigh_tridiagonal(a,b,eigvals_only=True,select='i',select_range=(nr-1,nr-1))[0]
            assert x<=float(radial_upper(d,nr,dr));rad.append(float(x))
        for route in ('ledger','paired'):
            lam,cap,safe=envelope(dr,dy,nr,route);omega=math.sqrt(float(lam));samples=[]
            for t in (1.,2.,6.,12.):
                K,N,_=normal(t,dy,ny,route);I=sp.eye(K.shape[0],format='csr');Z=N-1.5*I
                n0,n1=norm(Z),norm(Z+omega*K)
                assert max(n0,n1)<=float(cap)*(1+1e-12)
                g=[max(moving(t,h,dy,ny,w,route) for w in (0.,omega)) for h in (dt,float(safe))]
                samples.append(dict(t=t,n0=n0,n1=n1,historical_gain=g[0],safe_gain=g[1]))
            records.append(dict(dr=dr,dy=dy,ny=ny,nr=nr,route=route,lambda_max=rad,lambda_upper=float(lam),uniform_bound=float(cap),safe_dt=float(safe),historical_dt=dt,samples=samples))
    return records

def native_parity():
    from ksw668_f8_signed_route_stage import rhs,step
    rng=np.random.default_rng(1547);counts=0;er=0.;es=0.
    for dr,dy,ny,nr in ((.008,.012,7,9),(.006,.009,9,11)):
        j=np.arange(1,nr+1,dtype=float);hi=j+.5;lo=j-.5
        cp=np.zeros((3,nr+1));cm=cp.copy()
        for q,d in enumerate((3,7,11)):
            den=hi**d-lo**d;cp[q,1:]=d*hi**(d-1)/den;cm[q,1:]=d*lo**(d-1)/den
        src=np.zeros_like(cp)
        for q,d in enumerate((3,7,11)):
            diag,off=radial(d,nr,dr);vals,vec=eigh_tridiagonal(diag,off)
            j0=np.arange(nr);V=((j0+.5)**d-np.maximum(j0-.5,0)**d)/d
            for idx in (0,nr-1):
                omega=math.sqrt(vals[idx]);phi=vec[:,idx]/np.sqrt(V);phi/=max(abs(phi))
                for route in ('ledger','paired'):
                    for t in (1.,2.,12.):
                        T=clock(t);dt=.0003
                        def coeff(T):
                            u=brentq(lambda x:clock(x)-T,.5,14)
                            return -1/math.sqrt(1+u*u),1/u,0.
                        K,N,H=normal(t,dy,ny,route);H=H.copy();H[:ny]*=omega
                        x=rng.normal(size=3*ny);X=np.zeros((6,3,ny,nr+1));X[:3,q,:,:-1]=(x/H).reshape(3,ny,1)*phi
                        v,b,_=coeff(T);Y=rhs(X,dr,dy,b,v,0.,src,cp,cm,route)
                        expected=(((omega*K+N)@x)/H).reshape(3,ny,1)*phi
                        e=np.linalg.norm(Y[:3,q,:,:-1]-expected)/max(1.,np.linalg.norm(expected));er=max(er,e)
                        assert e<1e-10
                        def L(tau):
                            v,b,_=coeff(tau);K,N,J=normal(1/b,dy,ny,route);J=J.copy();J[:ny]*=omega
                            return sp.diags(H/J)@(omega*K+N)@sp.diags(J/H)
                        aa=x+dt*(L(T)@x);bb=.75*x+.25*(aa+dt*(L(T+dt)@aa));xx=(x+2*(bb+dt*(L(T+dt/2)@bb)))/3
                        out=step(X,T,dt,coeff,dr,dy,src,cp,cm,route)
                        want=(xx/H).reshape(3,ny,1)*phi
                        e=np.linalg.norm(out[:3,q,:,:-1]-want)/max(1.,np.linalg.norm(want));es=max(es,e);assert e<1e-10
                        counts+=1
    return dict(cases=counts,stage_error=er,step_error=es)


if __name__=='__main__':print(json.dumps(dict(modal=run(),native=native_parity()),indent=2))
