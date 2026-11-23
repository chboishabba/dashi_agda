"""Geometry-first mixed Gauss stages, no explicit mass inverse.
Classical Gauss collocation on the original canonical hp action.
The dense Gauss owner remains an independent finite reference.
"""
import numpy as np
from scipy.linalg import solve_banded
from check_f8_gauss_action import Gauss, a, b, exact_tableau


class BandedGauss(Gauss):
    def pack(self, x):
        # [stage, canonical component, node, mode, ...] -> [mode, node*4, ...]
        return x.transpose(3,2,0,1,*range(4,x.ndim)).reshape(self.n,4*self.fe.n,*x.shape[4:])

    def unpack(self, x):
        return x.reshape(self.n,self.fe.n,2,2,*x.shape[2:]).transpose(2,3,1,0,*range(4,x.ndim+2))

    def mixed(self,i):
        # P_i K_i = R_i X_i + f_i, X_i=x+h sum a_ij K_j.
        # P=[M,0; v C^T+D,I], R=[v C,I; -A,0].
        p,N=self.fe.p,self.fe.n; w=4*p+3
        mat=np.zeros((self.n,2*w+1,4*N)); ops=[]
        I=np.zeros((2*p+1,N));I[p]=1
        def add(row,col,B,s):
            for k in range(-p,p+1):
                j=np.arange(max(0,-k),min(N,N-k));d=4*k+row-col
                if B.ndim==2:mat[:,w+d,4*j+col]+=s*B[p+k,j]
                else:mat[:,w+d,4*j+col]+=s*B[:,p+k,j]
        for t in range(2):
            M,C,K,z,v,acc,g=self.stage[self.gauss_start+2*i+t]
            CT=np.zeros_like(C)
            for k in range(-p,p+1):
                j=np.arange(max(0,-k),min(N,N-k));CT[p+k,j]=C[p-k,j+k]
            B=v*CT;B[p,-1]+=(z+self.fe.Y[-1])**-3
            A=(1-v*v)*K+self.k2[:,None,None]*M
            ops.append((v*C,A,g))
            add(2*t,2*t,M,1);add(2*t+1,2*t,B,1);add(2*t+1,2*t+1,I,1)
            for j in range(2):
                h=-self.dt*a[t,j]
                add(2*t,2*j,v*C,h);add(2*t,2*j+1,I,h);add(2*t+1,2*j,A,-h)
        return mat,ops,w

    def apply_A(self,A,x,transpose=False):
        # x [node, mode, ...]; symmetric A (assembled mass/stiffness)
        p=self.fe.p; out=A[:,p,:].T[(...,)+(None,)*(x.ndim-2)]*x
        for k in range(1,p+1):
            out[:-k]+=A[:,p-k,k:].T[(...,)+(None,)*(x.ndim-2)]*x[k:]
            out[k:]+=A[:,p+k,:-k].T[(...,)+(None,)*(x.ndim-2)]*x[:-k]
        return out

    def apply_C(self,C,x,transpose=False):
        shape=x.shape
        return np.stack([self.fe.mv(C,x[:,:,j],transpose) for j in range(shape[2])],axis=-1) if x.ndim==3 else self.fe.mv(C,x,transpose)

    def solve_mixed(self,mat,rhs,w,transpose=False):
        if transpose:
            m=np.zeros_like(mat);N=mat.shape[-1]
            for k in range(-w,w+1):
                j=np.arange(max(0,-k),min(N,N-k));m[:,w+k,j]=mat[:,w-k,j+k]
            mat=m
        return np.stack([solve_banded((w,w),mat[i],rhs[i],check_finite=False,overwrite_ab=True) for i in range(self.n)])

    def advance(self,x,i,forced=True):
        mat,ops,w=self.mixed(i);u,m=x
        rhs=[]
        for C,A,g in ops:
            r=np.array([self.fe.mv(C,u)+m,-self.apply_A(A,u)])
            if forced:r[1,0]+=g*self.src
            rhs.append(r)
        K=self.unpack(self.solve_mixed(mat,self.pack(np.array(rhs)),w))
        return x+self.dt*np.einsum('s,sunm->unm',b,K)

    def reverse_flat(self,y,i):
        mat,ops,w=self.mixed(i)
        lam=y.transpose(1,0,2).reshape(2,self.fe.n,self.n,-1)
        rhs=self.dt*b[:,None,None,None,None]*lam[None]
        Z=self.unpack(self.solve_mixed(mat,self.pack(rhs),w,True))
        gain=np.zeros((self.n,y.shape[-1]));old=lam.copy()
        for t,(C,A,g) in enumerate(ops):
            alpha,beta=Z[t]
            old[0]+=self.apply_C(C,alpha,True)-self.apply_A(A,beta)
            old[1]+=alpha;gain+=g*self.src[:,None]*beta[0]
        return old.reshape(self.d,self.n,-1).transpose(1,0,2),gain

    def parity(self):
        rng=np.random.default_rng(2026);x=rng.normal(size=(2,self.fe.n,self.n));y=rng.normal(size=(self.n,self.d,4))
        def err(a,b):return np.linalg.norm(a-b)/max(np.linalg.norm(b),1e-300)
        errors=[]
        for i in sorted({0,1,self.nt//2,self.nt-1}):
            v=self.advance(x,i);ref=Gauss.advance(self,x,i)
            z,g=self.reverse_flat(y,i);zr,gr=Gauss.reverse_flat(self,y,i)
            errors.append([err(v,ref),err(z,zr),err(g,gr)])
        print('dense forward/reverse/source parity',np.max(errors,axis=0),flush=True)
        assert np.max(errors)<1e-9

    def run_banded(self,parity=False):
        if parity:self.parity()
        x=self.forward();W,F,R=self.weights();jets=self.jets(x)
        gain=self.adjoints([self.terminal(w) for w in W.values()])
        for j,(name,w) in enumerate(W.items()):
            f=np.sum(w*jets,axis=(0,1));err=np.linalg.norm(f-gain[:,j])/max(np.linalg.norm(f),1e-300)
            print(name,'forward',f.sum(),'adjoint',gain[:,j].sum(),'relative modal error',err,flush=True)
            assert err<1e-8
        print('wall flux',np.sum(F*jets),'bulk residual',np.sum(R*jets),flush=True)


if __name__=='__main__':
    import sys
    exact_tableau()
    args=(int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),float(sys.argv[4])) if len(sys.argv)>1 else (12,3,2,.005)
    S=BandedGauss(*args);print('grid',args,'steps',S.nt,'dt',S.dt,flush=True)
    S.run_banded('parity' in sys.argv or len(sys.argv)==1)
