"""Two-stage Gauss-Legendre F8 hp action: dense reference, not native FV.
Classical Gauss collocation / Runge-Kutta quadratic invariant identity.
Reuses original FE, canonical action, source, terminal jets and receivers.
"""
import numpy as np
import sympy as s
from math import asinh, sqrt
from scipy.optimize import brentq
from check_f8_geometric_adjoint import Solver

c = np.array([.5-sqrt(3)/6, .5+sqrt(3)/6])
a = np.array([[.25, .25-sqrt(3)/6], [.25+sqrt(3)/6, .25]])
b = np.array([.5, .5])


def exact_tableau():
    q = s.sqrt(3)/6
    A = s.Matrix([[s.Rational(1,4),s.Rational(1,4)-q],
                  [s.Rational(1,4)+q,s.Rational(1,4)]])
    B = s.Matrix([s.Rational(1,2)]*2)
    C = A*s.ones(2,1)
    C2 = C.applyfunc(lambda x:x**2)
    C3 = C.applyfunc(lambda x:x**3)
    terms = [B.dot(s.ones(2,1)), B.dot(C), B.dot(C2), B.dot(A*C),
             B.dot(C3), B.dot(A*C2), B.dot(s.diag(*C)*A*C), B.dot(A*A*C)]
    assert [s.simplify(t) for t in terms] == list(map(s.Rational, ['1','1/2','1/3','1/6','1/4','1/12','1/8','1/24']))
    assert all(s.simplify(B[i]*A[i,j]+B[j]*A[j,i]-B[i]*B[j])==0 for i in range(2) for j in range(2))
    print('PASS eight order conditions and four quadratic-invariant identities',flush=True)


class Gauss(Solver):
    def __init__(self,n,ne,p,dt,R=4.3,tfinal=11.8):
        super().__init__(n,ne,p,dt,R,tfinal)
        self.d=2*self.fe.n
        F=lambda t:asinh(t)-sqrt(1+t*t)/t
        T0=F(1)
        # Same original stage geometry/source, evaluated at actual Gauss nodes.
        def geometry(ds):
            t=brentq(lambda t:F(t)-T0-ds,.5,14)
            z=1/t;v=-1/sqrt(1+t*t);acc=t**3/(1+t*t)**2
            amp=-6*sqrt(1-v*v)/z*np.exp(1-1/(1-(2*ds/.065-1)**2)) if 0<ds<.065 else 0.
            M,C,K=self.fe.matrices(z,v)
            return M,C,K,z,v,acc,-z**-3*amp
        # Keep original endpoint indices for inherited jets/terminal/weights.
        for j in (0,self.nt,2*self.nt):
            for v,w in zip(self.stage[j],geometry(j*self.dt/2)):
                assert np.allclose(v,w,rtol=1e-13,atol=1e-14)
        self.gauss_start=len(self.stage)
        self.stage.extend(geometry((j+ci)*self.dt) for j in range(self.nt) for ci in c)

    def flat(self,x):
        return x.reshape(self.d,self.n).T

    def unflat(self,x):
        return x.T.reshape(2,self.fe.n,self.n)

    def operators(self,j):
        M,C,K,z,v,acc,g=self.stage[j]
        I=np.eye(self.fe.n)
        M,C,K=(self.fe.mv(B,I) for B in (M,C,K))
        D=np.zeros_like(M);D[-1,-1]=(z+self.fe.Y[-1])**-3
        N=np.linalg.solve(M,I);V=N@(v*C);B=v*C.T+D
        A=(1-v*v)*K+self.k2[:,None,None]*M
        L=np.empty((self.n,self.d,self.d));m=self.fe.n
        L[:,:m,:m]=V;L[:,:m,m:]=N
        L[:,m:,:m]=-B@V-A;L[:,m:,m:]=-B@N
        f=np.zeros((self.n,self.d));f[:,m]=g*self.src
        H=np.empty_like(L)
        H[:,:m,:m]=v*C.T@V+A;H[:,:m,m:]=v*C.T@N
        H[:,m:,:m]=V;H[:,m:,m:]=N
        return L,f,H,np.broadcast_to(D,(self.n,*D.shape))

    def system(self,i,frozen=False):
        j0=self.gauss_start+2*i
        ids=[2*i+1]*2 if frozen else [j0,j0+1]
        ops=[self.operators(j) for j in ids]
        L,f,H,D=(np.stack(v,axis=1) for v in zip(*ops))
        d=self.d
        B=np.zeros((self.n,2*d,2*d))
        for k in range(2):
            for l in range(2):
                B[:,k*d:(k+1)*d,l*d:(l+1)*d]=-self.dt*a[k,l]*L[:,k]
                if k==l:B[:,k*d:(k+1)*d,l*d:(l+1)*d]+=np.eye(d)
        return L,f,H,D,B

    def advance(self,x,i,forced=True,frozen=False,details=False):
        L,f,H,D,B=self.system(i,frozen)
        if not forced:f=np.zeros_like(f)
        y=self.flat(x)
        rhs=np.einsum('msij,mj->msi',L,y)+f
        K=np.linalg.solve(B,rhs.reshape(self.n,2*self.d,1)).reshape(self.n,2,self.d)
        X=y[:,None,:]+self.dt*np.einsum('st,mti->msi',a,K)
        new=y+self.dt*np.einsum('s,msi->mi',b,K)
        if details:return self.unflat(new),(y,new,X,K,L,f,H,D,B,rhs)
        return self.unflat(new)

    def reverse_flat(self,y,i):
        L,f,H,D,B=self.system(i)
        # y is [mode, canonical coordinate, receiver].
        rhs=(self.dt*b[None,:,None,None]*y[:,None,:,:]).reshape(self.n,2*self.d,-1)
        Z=np.linalg.solve(B.transpose(0,2,1),rhs).reshape(self.n,2,self.d,-1)
        return y+np.einsum('msij,msir->mjr',L,Z),np.einsum('msi,msir->mr',f,Z)

    def forward(self):
        x=np.zeros((2,self.fe.n,self.n))
        for i in range(self.nt):x=self.advance(x,i)
        assert np.isfinite(x).all()
        return x

    def adjoints(self,terminal):
        y=np.stack([self.flat(v) for v in terminal],axis=-1)
        gain=np.zeros((self.n,len(terminal)))
        for i in range(self.nt-1,-1,-1):
            y,g=self.reverse_flat(y,i);gain+=g
        return gain

    def adjoint(self,lam):
        return self.adjoints([lam])[:,0]

    def checks(self):
        rng=np.random.default_rng(20261120)
        x=rng.normal(size=(2,self.fe.n,self.n));y=rng.normal(size=x.shape)
        maximum=np.zeros(5)
        for i in sorted({0,min(1,self.nt-1),self.nt//2,self.nt-1}):
            for j in (self.gauss_start+2*i,self.gauss_start+2*i+1):
                L,f,_,_=self.operators(j)
                r=self.flat(self.rhs(x,j));ref=np.einsum('mij,mj->mi',L,self.flat(x))+f
                maximum[0]=max(maximum[0],np.linalg.norm(r-ref)/max(1.,np.linalg.norm(r)))
            z,data=self.advance(x,i,False,details=True)
            rev,_=self.reverse_flat(self.flat(y)[:,:,None],i)
            l=np.sum(z*y);r=np.sum(self.flat(x)*rev[:,:,0])
            maximum[1]=max(maximum[1],abs(l-r)/max(1.,abs(l),abs(r)))
            for frozen in (False,True):
                _,(old,new,X,K,L,f,H,D,B,rhs)=self.advance(x,i,True,frozen,True)
                resid=np.einsum('mij,mj->mi',B,K.reshape(self.n,-1))-rhs.reshape(self.n,-1)
                maximum[2]=max(maximum[2],np.linalg.norm(resid)/max(1.,np.linalg.norm(rhs)))
                E=lambda H,x:.5*np.einsum('mi,mij,mj->m',x,H,x)
                H0=H[:,0] if frozen else self.operators(2*i)[2]
                H1=H[:,0] if frozen else self.operators(2*i+2)[2]
                Hr=H[:,0] if frozen else self.operators(2*i+1)[2]
                vel=K[:,:,:self.fe.n]
                power=np.einsum('msi,msi->ms',vel,f[:,:,self.fe.n:])-np.einsum('msi,msij,msj->ms',vel,D,vel)
                work=self.dt*np.einsum('s,ms->m',b,power)
                geom=E(H1-Hr,new)+E(Hr-H0,old)+self.dt*np.einsum('s,msi,msij,msj->m',b,X,Hr[:,None]-H,K)
                delta=E(H1,new)-E(H0,old)
                err=np.max(abs(delta-work-geom)/(1e-30+abs(E(H1,new))+abs(E(H0,old))+abs(work)+abs(geom)))
                index=3 if frozen else 4;maximum[index]=max(maximum[index],err)
        assert np.max(maximum)<1e-9,maximum
        print('PASS operator, transpose, stage residual, frozen energy, moving energy ledger',maximum,flush=True)
        state=self.forward();jets=self.jets(state);W,F,R=self.weights()
        gain=self.adjoints([self.terminal(w) for w in W.values()])
        for j,(name,w) in enumerate(W.items()):
            f=np.sum(w*jets,axis=(0,1));err=np.linalg.norm(f-gain[:,j])/max(np.linalg.norm(f),1e-300)
            assert err<1e-8,(name,err)
            print(name,'forward',f.sum(),'adjoint',gain[:,j].sum(),'relative modal error',err,flush=True)
        return state


def convergence(n=12,ne=3,p=2):
    states=[];receivers=[];dts=[]
    # Exact dyadic step counts on fixed physical final time.
    span=asinh(11.8)-sqrt(1+11.8**2)/11.8-asinh(1)+sqrt(2)
    for steps in (540,1080,2160,4320):
        S=Gauss(n,ne,p,span/(steps-.01));assert S.nt==steps
        x=S.forward();W,_,_=S.weights();jets=S.jets(x)
        states.append(x);receivers.append(np.array([np.sum(w*jets,axis=(0,1)) for w in W.values()]));dts.append(S.dt)
        print('refine',n,ne,p,steps,S.dt,'receiver sums',receivers[-1].sum(axis=1),flush=True)
    for label,values in [('state',states),('modal receiver',receivers)]:
        errors=[np.linalg.norm(x-y) for x,y in zip(values,values[1:])]
        orders=np.log2(np.array(errors[:-1])/errors[1:]);print(label,'differences',errors,'orders',orders,flush=True)
        assert orders[-1]>3.7,(label,orders)


if __name__=='__main__':
    import sys
    exact_tableau()
    if len(sys.argv)>1 and sys.argv[1]=='refine':convergence()
    else:
        args=(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),float(sys.argv[4])) if len(sys.argv)>1 else (12,3,2,.005)
        S=Gauss(*args);print('grid',args,'steps',S.nt,'dt',S.dt,flush=True);S.checks()
