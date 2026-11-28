#!/usr/bin/env python3
"""BR30: actual projected 35+9 dynamic transmission resolvent.
Constant-coefficient periodic normal interval; not constrained Einstein evolution.
"""
import numpy as np
from scipy.linalg import cholesky,eigh,expm,solve
from numpy.polynomial.legendre import leggauss
from check_hopf369_br_curvature_energy import carrier


def prepare():
    _,_,_,G,_,H,J,A,B,R,_,_=carrier()
    mat=lambda M:np.array(M.tolist(),dtype=float)
    g=cholesky(mat(G),lower=False);h=cholesky(mat(H),lower=False)
    gi=np.linalg.inv(g);hi=np.linalg.inv(h)
    A=[g@mat(a)@gi for a in A];B=[h@mat(b)@hi for b in B]
    lam,U=eigh(A[3]); act=np.flatnonzero(abs(lam)>1e-8);zero=np.flatnonzero(abs(lam)<=1e-8)
    U=U[:,np.r_[act,zero]];lam=lam[np.r_[act,zero]]
    assert len(act)==26 and len(zero)==9
    A=[U.T@a@U for a in A];J=U.T@g@mat(J)@hi;R=h@mat(R)@gi@U
    assert np.max(abs(R[:,26:]))<1e-12
    assert np.max(abs(np.diag(lam)@J-3*R.T))<1e-12
    return lam,A,B,J,R


def run():
    lam,A,B,J,R=prepare(); j=-1.2;c=-3*j;L=2*np.log(2)
    rng=np.random.default_rng(369);cases=0; worst=0.;worst_bc=0.
    xx,ww=leggauss(64);xx=(xx+1)*L/2;ww=ww*L/2
    for s0 in (.4,1.2,-.7):
        for k in ((0,0,0),(1,-2,1),(2,1,0)):
            f=rng.standard_normal(35)+1j*rng.standard_normal(35)
            fwall=rng.standard_normal(9)+1j*rng.standard_normal(9)
            T=s0*np.eye(35,dtype=complex)-1j*sum((k[i]*A[i] for i in range(3)),np.zeros((35,35)))
            T00=T[26:,26:];z0=solve(T00,f[26:]);Z=-solve(T00,T[26:,:26]);
            O=(T[:26,:26]+T[:26,26:]@Z)/lam[:26,None]
            g=(T[:26,26:]@z0-f[:26])/lam[:26]
            aug=np.zeros((27,27),complex);aug[:26,:26]=O;aug[:26,26]=g
            def transfer(x):
                V=expm(x*aug);return V[:26,:26],V[:26,26]
            P,q=transfer(L)
            lift=np.vstack([np.eye(26),Z]);base=np.r_[np.zeros(26),z0]
            wall=s0*np.eye(9,dtype=complex)-1j*sum((k[i]*B[i] for i in range(3)),np.zeros((9,9)))
            S=np.block([[np.eye(26)-P,-j*J[:26,:]],[R@lift@(np.eye(26)+P)/2,wall]])
            rhs=np.r_[q,fwall-R@(base+lift@q/2)]
            a0m=solve(S,rhs);a0=a0m[:26];m=a0m[26:]
            def field(x):
                T0,q0=transfer(x);return lift@(T0@a0+q0)+base
            wp=field(0);wm=field(L);mean=(wp+wm)/2
            bc=max(np.max(abs((wp-wm-j*J@m)[:26])),np.max(abs(wall@m+R@mean-fwall)))
            worst_bc=max(worst_bc,bc)
            norm=c*np.vdot(m,m).real;work=c*np.vdot(m,fwall).real;fnorm=c*np.vdot(fwall,fwall).real+L*np.vdot(f,f).real
            for x,w in zip(xx,ww):
                u=field(x);norm+=w*np.vdot(u,u).real;work+=w*np.vdot(u,f).real
            err=abs(s0*norm-work)/max(1,abs(work),abs(s0*norm));worst=max(worst,err)
            assert err<2e-8 and bc<2e-8
            assert s0*s0*norm<=fnorm*(1+2e-8)
            cases+=1
    print('PASS',cases,'full 35x35 dynamic resolvents (both real signs, zero and nonzero tangential frequency)')
    print('max relative energy residual',worst,'max boundary residual',worst_bc)

if __name__=='__main__':run()
