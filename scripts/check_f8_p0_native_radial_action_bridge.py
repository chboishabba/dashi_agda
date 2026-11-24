"""F8 P0 same-carrier action bridge: original normal hp FE, exact original
 d=3,7,11 finite-volume radial stiffness and actual compact FV source.
 A finite semidiscrete construction comparator, NOT original production replay.
"""
import json
from math import sqrt,asinh
import numpy as np
from scipy.optimize import brentq
from scipy.linalg import solve_banded
from check_f8_geometry_hp import FE
from ksw668_f8_full_coupled_weighted_sbp_energy import radial_stiffness
from ksw668_f8_fv_source_flux import exact_cell_averages
DIMS=(3,7,11)

def F(t):return asinh(t)-sqrt(1+t*t)/t

def source_clock(t):
    ds=F(t)-F(1)
    return np.exp(1-1/(1-(2*ds/.065-1)**2)) if 0<ds<.065 else 0.

def geometry(t):
    b=1/t;v=-1/sqrt(1+t*t);vt=t**3/(1+t*t)**2
    return b,v,vt

class NativeAction:
    def __init__(self,ne=4,p=1,nr=9,dr=.008):
        self.fe=FE(ne,p);self.nr=nr;self.dr=dr;self.eps=.04
        self.L=[];self.V=[]
        for d in DIMS:
            l,vol=radial_stiffness(d,nr,dr)
            assert np.max(abs(vol[:,None]*l-l.T*vol[None,:])) <= 5e-12*max(1.,np.max(abs(vol[:,None]*l)),np.max(abs(l.T*vol[None,:])))
            self.L.append(l);self.V.append(vol)
        self.V=np.array(self.V)
        self.S=exact_cell_averages(self.eps,np.arange(nr)*dr,dr)
    def apply(self,B,U,transpose=False):
        return np.stack([self.fe.mv(B,U[i],transpose) for i in range(3)])
    def matrices(self,t,derivative=False):
        b,v,vt=geometry(t)
        return self.fe.matrices(b,v,derivative)
    def solveM(self,M,R):
        return np.stack([solve_banded((self.fe.p,self.fe.p),M,R[i],check_finite=False) for i in range(3)])
    def radial(self,U):return np.stack([U[i]@self.L[i].T for i in range(3)])
    def rhs(self,t,U,m,forced=True):
        b,v,vt=geometry(t);M,C,K=self.matrices(t)
        W=self.solveM(M,m+v*self.apply(C,U))
        radial=self.apply(M,self.radial(U))
        md=-v*self.apply(C,W,True)-(1-v*v)*self.apply(K,U)+radial
        amp=-6*sqrt(1-v*v)/b*source_clock(t)
        if forced:md[:,0,:]-=b**-3*amp*self.S
        md[:,-1,:]-=(b+self.fe.Y[-1])**-3*W[:,-1,:]
        return W,md
    def energy(self,t,U,m):
        b,v,vt=geometry(t);M,C,K=self.matrices(t)
        W=self.solveM(M,m+v*self.apply(C,U))
        rad=self.radial(U)
        mw=self.apply(M,W);ku=self.apply(K,U);mr=self.apply(M,rad)
        return .5*float(np.sum(self.V*(np.einsum('ijk,ijk->ik',W,mw)+(1-v*v)*np.einsum('ijk,ijk->ik',U,ku)-np.einsum('ijk,ijk->ik',U,mr))))
    def ledger(self,t,U,m,forced=True):
        b,v,vt=geometry(t);M,C,K=self.matrices(t);Md,Cd,Kd=self.matrices(t,True)
        W,md=self.rhs(t,U,m,forced);rad=self.radial(U)
        # E' from the time-dependent canonical momentum and geometry.
        # Induced boundary work is recorded separately from the moving mass.
        source=np.zeros_like(md)
        amp=-6*sqrt(1-v*v)/b*source_clock(t)
        if forced:source[:,0,:]-=b**-3*amp*self.S
        source[:,-1,:]-=(b+self.fe.Y[-1])**-3*W[:,-1,:]
        terms={}
        def dot(a,b):return float(np.sum(self.V*np.einsum('ijk,ijk->ik',a,b)))
        terms['source_work']=dot(W,source)
        terms['moving_mass']=-.5*dot(W,self.apply(Md,W))
        terms['moving_momentum']=vt*dot(W,self.apply(C,U))+v*dot(W,self.apply(Cd,U))
        terms['moving_normal_stiffness']=.5*(1-v*v)*dot(U,self.apply(Kd,U))-v*vt*dot(U,self.apply(K,U))
        terms['moving_radial_mass']=-.5*dot(U,self.apply(Md,rad))
        expected=sum(terms.values())
        def geometryE(z):return self.energy(brentq(lambda t:F(t)-z,1.,1.3),U,m)
        T=F(t);delta=1.e-6
        partial=(geometryE(T+delta)-geometryE(T-delta))/(2*delta)
        # directional gradient wrt state via E(t,U+eps W,m+eps md)
        eps=1.e-6
        directional=(self.energy(t,U+eps*W,m+eps*md)-self.energy(t,U-eps*W,m-eps*md))/(2*eps)
        residual=partial+directional-expected
        return dict(E=self.energy(t,U,m),analytical_Eprime=expected,estimated_Eprime=partial+directional,error=residual,terms=terms,source_nonzero=bool(np.any(self.S)),source_amplitude=amp)

def audit():
    t=brentq(lambda u:F(u)-F(1)-.0325,1,1.3)
    rows=[]
    for ne,nr,dr in ((4,9,.008),(6,12,.006),(8,15,.004)):
        r=NativeAction(ne=ne,nr=nr,dr=dr)
        rng=np.random.default_rng(84)
        U=rng.normal(size=(3,r.fe.n,r.nr))*.01
        m=rng.normal(size=U.shape)*.01
        on=r.ledger(t,U,m,True);off=r.ledger(t,U,m,False)
        assert abs(on['error'])<2e-6 and abs(off['error'])<2e-6,(on,off)
        assert abs(on['terms']['source_work']-off['terms']['source_work'])>1e-9
        assert np.array_equal(r.S[:,int(np.ceil(.04/dr+1)):], np.zeros_like(r.S[:,int(np.ceil(.04/dr+1)):]))
        assert all(np.all(np.linalg.eigvalsh(-np.sqrt(r.V[i])[:,None]*r.L[i]/np.sqrt(r.V[i])[None,:])>0) for i in range(3))
        assert all(not np.array_equal(r.L[i],r.L[j]) for i in range(3) for j in range(i+1,3))
        # Independent physical source load into the exact canonical energy ledger.
        assert abs(on['terms']['source_work']-off['terms']['source_work'])>0
        rows.append(dict(ne=ne,nr=nr,dr=dr,source_on=on,source_off=off,
            source_work_delta=on['terms']['source_work']-off['terms']['source_work']))
    return dict(status='PASS 3 meshes x source-on/off = 6 canonical forced-energy ledgers',
        t=t,dt_from_source_clock=.0325,DIMS=DIMS,rows=rows,
        limitations='Original-equivalent radial/FE/source operators, not literal production solver nor temporal solution, independent Weyl receiver, full stability or causal-null convergence')
if __name__=='__main__':print(json.dumps(audit(),indent=2))
