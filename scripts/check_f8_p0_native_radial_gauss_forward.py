"""Native FV radial eigenbasis and Gauss-2 action forward control.

All 3 original ell=0,2,4 / d=3,7,11 operators and original
conservative compact FV source. Reuses check_f8_p0_native_radial_action_bridge
(the existing geometric FE/Israel/moving energy owner).
Finite independent source-on/off Gauss trajectories across three short radial
boxes and four dt. NOT original t=12 near/far Weyl production, full
SSPRK3 equivalence, continuum signal or PDE theorem.
"""
import json
from math import sqrt
import numpy as np
from scipy.linalg import eigh, solve
from scipy.optimize import brentq
from check_f8_p0_native_radial_action_bridge import NativeAction,F,geometry

C=(.5-sqrt(3)/6,.5+sqrt(3)/6)
A=np.array([[.25,.25-sqrt(3)/6],[.25+sqrt(3)/6,.25]])
B=np.array([.5,.5])

class NativeGauss:
    def __init__(self,ne,nr,dr):
        self.phys=NativeAction(ne=ne,nr=nr,dr=dr)
        self.ny=self.phys.fe.n
        self.eigs=[];self.basis=[];self.src=[]
        for i in range(3):
            V=self.phys.V[i]
            root=np.sqrt(V)
            S=-(root[:,None]*self.phys.L[i])/root[None,:]
            assert np.max(abs(S-S.T))<1e-8
            val,R=eigh(S)
            assert min(val)>0
            Q=R/root[:,None]
            self.eigs.append(val)
            self.basis.append(Q)
            self.src.append(Q.T@(V*self.phys.S[i]))
            assert np.max(abs(Q.T@(V[:,None]*Q)-np.eye(nr)))<5e-12
            assert np.max(abs(self.phys.L[i]@Q+Q*val[None,:])) < 1e-12*np.max(abs(Q))*max(val)
            assert np.max(abs(Q@self.src[-1]-self.phys.S[i]))<1e-10*max(1,np.max(abs(self.phys.S[i])))
    def to_mode(self,X):
        return np.stack([X[i]@(self.phys.V[i][:,None]*self.basis[i]) for i in range(3)])
    def from_mode(self,X):
        return np.stack([X[i]@self.basis[i].T for i in range(3)])
    def stage(self,t,lam,src,forced):
        p=self.phys;M,C,K=p.matrices(t);b,v,vt=geometry(t)
        n=self.ny
        eye=np.eye(n)
        MM=np.column_stack([p.fe.mv(M,eye[:,i:i+1])[:,0] for i in range(n)])
        CC=np.column_stack([p.fe.mv(C,eye[:,i:i+1])[:,0] for i in range(n)])
        KK=np.column_stack([p.fe.mv(K,eye[:,i:i+1])[:,0] for i in range(n)])
        invM=np.linalg.inv(MM)
        Vmat=v*invM@CC
        D=np.zeros((n,n));D[-1,-1]=(b+p.fe.Y[-1])**-3
        Z=v*CC.T + D
        L=np.block([[Vmat,invM],[-Z@Vmat-(1-v*v)*KK-lam*MM,-Z@invM]])
        from check_f8_p0_native_radial_action_bridge import source_clock
        amp=-6*sqrt(1-v*v)/b*source_clock(t)
        f=np.zeros(2*n)
        if forced:f[n]=-b**-3*amp*src
        return L,f
    def clock_t(self,T):
        """Invert original monotone bulk clock on all t>=1 (including t=12)."""
        if T < F(1)-1e-12:
            raise ValueError("bulk time predates original brane t=1")
        hi=2.
        while F(hi)<T:
            hi*=2.
            if hi>1e9:
                raise ValueError("clock outside supported physical domain")
        return brentq(lambda t:F(t)-T,1.,hi)
    def step(self,y,T,h,ell,mode,forced):
        Lf=[self.stage(self.clock_t(T+h*ci),self.eigs[ell][mode],self.src[ell][mode],forced) for ci in C]
        sz=len(y);Z=np.eye(2*sz)
        for i in range(2):
            for j in range(2):
                Z[i*sz:(i+1)*sz,j*sz:(j+1)*sz]-=h*A[i,j]*Lf[i][0]
        rhs=np.concatenate([L@y+f for L,f in Lf])
        K=solve(Z,rhs,assume_a='gen').reshape(2,sz)
        return y+h*B@K
    def evolve(self,h,forced=True,Tmax=.068):
        T0=F(1);n=int(np.ceil(Tmax/h));dt=Tmax/n
        Y=np.zeros((3,self.ny,self.phys.nr));Z=Y.copy()
        for j in range(n):
            T=T0+j*dt
            for ell in range(3):
                for mode in range(self.phys.nr):
                    y=np.concatenate((Y[ell,:,mode],Z[ell,:,mode]))
                    new=self.step(y,T,dt,ell,mode,forced)
                    Y[ell,:,mode]=new[:self.ny];Z[ell,:,mode]=new[self.ny:]
        U=self.from_mode(Y);m=self.from_mode(Z)
        final_t=self.clock_t(T0+Tmax)
        return U,m,final_t,n
    def rhs_parity(self,t):
        rng=np.random.default_rng(23)
        U=rng.normal(size=(3,self.ny,self.phys.nr))*.001
        m=rng.normal(size=U.shape)*.001
        W,md=self.phys.rhs(t,U,m,True)
        Um=self.to_mode(U);mm=self.to_mode(m)
        Wr=np.zeros_like(Um);mr=np.zeros_like(mm)
        for ell in range(3):
            for mode in range(self.phys.nr):
                L,f=self.stage(t,self.eigs[ell][mode],self.src[ell][mode],True)
                out=L@np.r_[Um[ell,:,mode],mm[ell,:,mode]]+f
                Wr[ell,:,mode]=out[:self.ny];mr[ell,:,mode]=out[self.ny:]
        return max(float(np.max(np.abs(self.from_mode(Wr)-W))),float(np.max(np.abs(self.from_mode(mr)-md))))

def run():
    out=[]
    for ne,nr,dr in ((2,9,.008),(3,12,.006),(4,15,.004)):
        g=NativeGauss(ne,nr,dr)
        parity=g.rhs_parity(g.clock_t(F(1)+.0325))
        assert parity<1e-7,parity
        cases=[]
        for dt in (.004,.002,.001,.0005):
            U,m,t,n=g.evolve(dt,True,.068)
            Uoff,moff,toff,noff=g.evolve(dt,False,.068)
            assert np.array_equal(Uoff,np.zeros_like(Uoff)) and np.array_equal(moff,np.zeros_like(moff))
            assert np.all(np.isfinite(U)) and np.all(np.isfinite(m))
            assert np.linalg.norm(U)>0
            H=float(np.linalg.norm(U));E=g.phys.energy(t,U,m)
            assert E>=0
            cases.append(dict(dt_requested=dt,steps=n,clock_t=t,field_norm=H,
                              energy=E,source_off_exact_zero=True))
        out.append(dict(ne=ne,nr=nr,dr=dr,operator_rhs_max_diff=parity,cases=cases,
                        first_dt_field_difference=abs(cases[0]['field_norm']-cases[1]['field_norm']),
                        late_dt_field_difference=abs(cases[-2]['field_norm']-cases[-1]['field_norm'])))
    result=dict(status='PASS finite native-carrier 3 grids x 4 dt, original compact source on/off, two-stage implicit Gauss short-pulse forward',
        rows=out,limitations='No uniform spatial convergence; small radial boxes vary with dr and have outer boundary inside the original physical receiver. Short clock span .068 only, NOT original t12 near/far, mode3/mode4 parity, H4 trace, both Weyl or causal-null.')
    print(json.dumps(result,indent=2))
    return result
if __name__=='__main__':run()
