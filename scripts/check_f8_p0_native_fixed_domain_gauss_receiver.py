"""F8 P0 same-domain original-FV radial action/Gauss t=12 receiver experiment.

Reuses source-owned moving hp FE, d=3/7/11 weighted native FV radial
operators, conservative compact TT cell averages and physical F(t).
Batched Gauss-2 algebra has an independent old per-eigenmode one-step
parity test. Same radial domain r=0..3.0 at each dr; original t=12
near/far physical receiver events. No CI, original mode3/4 replay,
Weyl promotion or certified continuum convergence.
"""
import json
from math import sqrt
import numpy as np
from check_f8_p0_native_radial_gauss_forward import NativeGauss,F,geometry,A,B,C
from check_f8_p0_native_radial_action_bridge import source_clock

class BatchedNativeGauss(NativeGauss):
    def __init__(self,ne,nr,dr):
        super().__init__(ne,nr,dr)
        self.lam=np.concatenate(self.eigs)
        self.src_flat=np.concatenate(self.src)
        self.nmode=3*nr

    def blocks(self,t):
        p=self.phys
        M,Cmat,K=p.matrices(t)
        b,v,_=geometry(t)
        n=self.ny
        eye=np.eye(n)
        MM=np.column_stack([p.fe.mv(M,eye[:,i:i+1])[:,0] for i in range(n)])
        CC=np.column_stack([p.fe.mv(Cmat,eye[:,i:i+1])[:,0] for i in range(n)])
        KK=np.column_stack([p.fe.mv(K,eye[:,i:i+1])[:,0] for i in range(n)])
        invM=np.linalg.inv(MM)
        Vmat=v*invM@CC
        D=np.zeros((n,n));D[-1,-1]=(b+p.fe.Y[-1])**-3
        Z=v*CC.T+D
        L=np.zeros((self.nmode,2*n,2*n))
        L[:,:n,:n]=Vmat
        L[:,:n,n:]=invM
        L[:,n:,:n]=-Z@Vmat-(1-v*v)*KK-self.lam[:,None,None]*MM
        L[:,n:,n:]=-Z@invM
        amp=-6*sqrt(1-v*v)/b*source_clock(t)
        f=np.zeros((self.nmode,2*n))
        f[:,n]=-b**-3*amp*self.src_flat
        return L,f

    def one_step(self,X,T,h,forced=True):
        stages=[self.blocks(self.clock_t(T+h*ci)) for ci in C]
        n2=X.shape[1]
        mat=np.broadcast_to(np.eye(2*n2),(self.nmode,2*n2,2*n2)).copy()
        for i in range(2):
            for j in range(2):
                mat[:,i*n2:(i+1)*n2,j*n2:(j+1)*n2]-=h*A[i,j]*stages[i][0]
        rhs=np.concatenate([
            np.einsum('nij,nj->ni',L,X)+(f if forced else 0.)
            for L,f in stages],axis=1)
        # Explicit singleton last dimension for NumPy 2 vector-stack semantics.
        kval=np.linalg.solve(mat,rhs[:,:,None])[:,:,0]
        return X+h*(B[0]*kval[:,:n2]+B[1]*kval[:,n2:])

    def evolve_batched(self,h,span,forced=True):
        n=int(np.ceil(span/h));dt=span/n;T0=F(1)
        X=np.zeros((self.nmode,2*self.ny))
        for j in range(n):
            X=self.one_step(X,T0+j*dt,dt,forced)
        yy=X[:,:self.ny].reshape(3,self.phys.nr,self.ny).transpose(0,2,1)
        zz=X[:,self.ny:].reshape(3,self.phys.nr,self.ny).transpose(0,2,1)
        return self.from_mode(yy),self.from_mode(zz),self.clock_t(T0+span),n

def receiver(U,r,dr,eps):
    x=r/dr;j=int(np.floor(x));q=x-j
    if j-1<0 or j+2>=U.shape[-1]:
        raise ValueError('receiver outside four-node original stencil')
    w=np.array([-q*(q-1)*(q-2)/6,(q+1)*(q-1)*(q-2)/2,
                -(q+1)*q*(q-2)/2,(q+1)*q*(q-1)/6])
    raw=U[:,0,j-1:j+3]@w
    H=(r/eps)**np.array([0,2,4])*raw
    return dict(stencil=[j-1,j,j+1,j+2],phase=float(q),
                mode_raw_wall=raw.tolist(),mode_H=H.tolist(),
                signed_total_H=float(np.sum(H)))

def audit():
    probe=BatchedNativeGauss(2,9,.04)
    rng=np.random.default_rng(3)
    X=rng.normal(size=(probe.nmode,2*probe.ny))*.01
    T=F(1)+.03;h=.002
    batched=probe.one_step(X,T,h)
    serial=np.empty_like(batched)
    for ell in range(3):
        for mode in range(probe.phys.nr):
            k=ell*probe.phys.nr+mode
            serial[k]=probe.step(X[k],T,h,ell,mode,True)
    parity=float(np.max(abs(batched-serial)))
    assert parity<5e-12,parity
    rbulk=sqrt((F(12)-F(1))**2-(1-1/12)**2)
    span=F(12)-F(1)
    rows=[]
    for ne in (2,3):
        for dr in (.01,.008,.006):
            nr=round(3./dr)+1
            assert abs((nr-1)*dr-3.)<1e-12
            g=BatchedNativeGauss(ne,nr,dr)
            for dt in (.02,.01):
                U,m,t,n=g.evolve_batched(dt,span,True)
                Uoff,moff,_,_=g.evolve_batched(dt,span,False)
                assert np.array_equal(Uoff,np.zeros_like(Uoff))
                assert np.array_equal(moff,np.zeros_like(moff))
                assert abs(t-12)<1e-10
                assert np.isfinite(U).all() and np.isfinite(m).all()
                energy=float(g.phys.energy(t,U,m))
                assert np.isfinite(energy) and energy>=0
                values={}
                for label,r in (('near',rbulk-.012),('far',rbulk+.1)):
                    values[label]=receiver(U,r,dr,.04)
                rows.append(dict(ne=ne,nr=nr,dr=dr,requested_dt=dt,
                    actual_dt=span/n,steps=n,physical_receiver_t=t,
                    energy=energy,source_off_exact_zero=True,receivers=values))
    # A finite forbidden-field negative control, NOT causality closure.
    assert all(abs(x['receivers']['far']['signed_total_H'])>0 for x in rows)
    return dict(status='PASS finite fixed-domain original-source action/Gauss forward',
      radial_domain=[0,3.],normal_domain=[0,2.1],
      original_receiver_t=12,source_on_runs=len(rows),
      source_off_exact_zero_runs=len(rows),
      batched_vs_serial_one_step_abs_error=parity,
      rows=rows,physical_far_causal_null='FAIL finite',
      original_mode3_mode4_comparison='NOT_RUN',
      original_both_Weyl='NOT_EVALUATED',
      convergence='UNPROVED; nonmonotone across dr/dt and low-order normal FE',
      execution='Local source-equivalent owner modules must be run from literal PR checkout for authentic head acceptance')

if __name__=='__main__':
    print(json.dumps(audit(),indent=2))
