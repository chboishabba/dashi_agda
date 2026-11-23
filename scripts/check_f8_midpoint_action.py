"""Same-action implicit midpoint and exact reverse; F8 hp geometry, no continuum claim."""
import numpy as np
from scipy.linalg import solve_banded
from check_f8_geometric_adjoint import Solver

class Midpoint(Solver):
    def blocks(self,j):
        M,C,K,b,v,a,g=self.stage[j]; h=self.dt/2;c=1-v*v
        D=np.zeros_like(M);D[self.fe.p,-1]=(b+self.fe.Y[-1])**-3
        CT=np.zeros_like(C);p=self.fe.p
        for k in range(-p,p+1):
            if k>=0:CT[p+k,:self.fe.n-k]=C[p-k,k:]
            else:CT[p+k,-k:]=C[p-k,:self.fe.n+k]
        A=c*K[:,:,None]+M[:,:,None]*self.k2
        L=(M+h*(v*(CT-C)+D))[:,:,None]+h*h*A
        return M,C,D,A,L,v,g
    def solve_modes(self,L,r,transpose=False):
        p=self.fe.p;n=self.fe.n
        if transpose:
            Z=np.zeros_like(L)
            for k in range(-p,p+1):
                if k>=0:Z[p+k,:n-k]=L[p-k,k:]
                else:Z[p+k,-k:]=L[p-k,:n+k]
            L=Z
        return np.stack([solve_banded((p,p),L[:,:,i],r[:,i],check_finite=False) for i in range(self.n)],axis=1)
    def amv(self,A,u):
        p=self.fe.p;y=A[p]*u
        for k in range(1,p+1):
            y[:-k]+=A[p-k,k:]*u[k:];y[k:]+=A[p+k,:-k]*u[:-k]
        return y
    def advance(self,x,j,forced=True):
        M,C,D,A,L,v,g=self.blocks(j);h=self.dt/2;u,m=x;mv=self.fe.mv
        f=np.zeros_like(u)
        if forced:f[0]=g*self.src
        q=self.solve_modes(L,m+v*mv(C,u)-h*self.amv(A,u)+h*f)
        du=self.dt*q;dm=self.dt*(-v*mv(C,q,True)-mv(D,q)-self.amv(A,u+h*q)+f)
        return x+np.array([du,dm]),q
    def reverse(self,y,j):
        M,C,D,A,L,v,g=self.blocks(j);h=self.dt/2;dt=self.dt;alpha,beta=y;mv=self.fe.mv
        r=self.solve_modes(L,dt*(alpha-v*mv(C,beta)-mv(D,beta)-h*self.amv(A,beta)),True)
        return np.array([alpha-dt*self.amv(A,beta)+v*mv(C,r,True)-h*self.amv(A,r),beta+r]),g*self.src*(dt*beta[0]+h*r[0])
    def energy(self,x,j):
        M,C,K,b,v,a,g=self.stage[j];u,m=x;mv=self.fe.mv;q=self.solve(M,m+v*mv(C,u))
        return .5*np.sum(q*mv(M,q)+(1-v*v)*u*mv(K,u)+u*mv(M,u)*self.k2,axis=0)
    def forward(self):
        x=np.zeros((2,self.fe.n,self.n));xmax=0.
        for i in range(self.nt):
            j=2*i+1;y,q=self.advance(x,j);M,C,D,A,L,v,g=self.blocks(j)
            old,new=self.energy(x,j),self.energy(y,j)
            work=self.dt*(g*self.src*q[0]-np.sum(q*self.fe.mv(D,q),axis=0))
            err=np.max(abs(new-old-work)/(1e-30+abs(old)+abs(new)+abs(work)))
            xmax=max(xmax,err);x=y
        print('max midpoint energy identity relative defect',xmax,flush=True);assert xmax<1e-8
        return x
    def adjoint(self,lam):
        gain=np.zeros(self.n)
        for i in range(self.nt-1,-1,-1):lam,g=self.reverse(lam,2*i+1);gain+=g
        return gain
    def run_checks(self):
        rng=np.random.default_rng(2026);x=rng.normal(size=(2,self.fe.n,self.n));y=rng.normal(size=x.shape)
        z,q=self.advance(x,1,False);p,g=self.reverse(y,1)
        err=abs(np.sum(z*y)-np.sum(x*p))/max(1,abs(np.sum(z*y)),abs(np.sum(x*p)))
        assert err<1e-10;print('one-step transpose relative defect',err,flush=True)
        x=self.forward();jets=self.jets(x);W,F,R=self.weights()
        for name,w in W.items():
            f=np.sum(w*jets,axis=(0,1));g=self.adjoint(self.terminal(w));err=np.linalg.norm(f-g)/max(np.linalg.norm(f),1e-300)
            assert err<1e-8;print(name,'forward',f.sum(),'adjoint',g.sum(),'relative modal error',err,flush=True)
        print('wall flux',np.sum(F*jets),'bulk residual',np.sum(R*jets),flush=True)

if __name__=='__main__':
    import sys
    n,ne,p,dt=(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),float(sys.argv[4])) if len(sys.argv)>1 else (90,10,3,.01)
    S=Midpoint(n,ne,p,dt);print('grid',n,ne,p,'dt',S.dt,'steps',S.nt,flush=True);S.run_checks()
