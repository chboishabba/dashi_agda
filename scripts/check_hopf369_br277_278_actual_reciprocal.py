"""Actual BR240 history: BR270 assembled derivative and BR271 six-face residual.
Finite directional variation and affine history, not coupled Einstein evolution.
"""
import argparse
from itertools import product, permutations, combinations
import numpy as np
from scipy.interpolate import RegularGridInterpolator
from numpy.polynomial.legendre import leggauss
from check_hopf369_br240_metric_history import run


def assembly(g,dg):
    from check_hopf369_p0ag import z
    grid=np.linspace(-1.5,1.5,g.shape[0]); sample=RegularGridInterpolator((grid,)*3,g[...,:4,:4]); tangent=RegularGridInterpolator((grid,)*3,dg[...,:4,:4])
    M=np.zeros((54,54)); Ma=M.copy(); N=np.zeros((36,36)); L=np.zeros((54,36)); dM=M.copy(); dMa=M.copy(); dN=N.copy(); dL=L.copy()
    t,w=leggauss(3);t=(t+1)/2;w=w/2
    for p in z.cells:
        for ijk in product(range(3),repeat=3):
            x=t[list(ijk)]; e,b=z.basis(p,x); X=np.array(p)+x-1; G=sample(X)[0]; U=tangent(X)[0]; h=G[1:,1:]; dh=U[1:,1:]; I=np.linalg.inv(h); beta=I@G[0,1:]; dbeta=I@(U[0,1:]-dh@beta)
            alpha=np.sqrt(beta@h@beta-G[0,0]); da=(2*beta@U[0,1:]-beta@dh@beta-U[0,0])/(2*alpha); r=np.sqrt(np.linalg.det(h)); dr=r*np.trace(I@dh)/2
            W=r*I; dW=dr*I-r*I@dh@I; V=h/r; dV=dh/r-h*dr/r**2; wt=np.prod(w[list(ijk)])
            cross=np.cross(beta,b.T).T; dcross=np.cross(dbeta,b.T).T
            M+=wt*e.T@W@e; dM+=wt*e.T@dW@e; Ma+=wt*alpha*e.T@W@e; dMa+=wt*e.T@(da*W+alpha*dW)@e
            N+=wt*alpha*b.T@V@b; dN+=wt*b.T@(da*V+alpha*dV)@b; L+=wt*(W@e).T@cross; dL+=wt*((dW@e).T@cross+(W@e).T@dcross)
    K=np.linalg.inv(M); dK=-K@dM@K; H=np.block([[K@Ma@K,K@L],[L.T@K,N]])
    dH=np.block([[dK@Ma@K+K@dMa@K+K@Ma@dK,dK@L+K@dL],[(dK@L+K@dL).T,dN]])
    return H,dH


def material():
    gs,_=run(11,full=True); g=gs[-1]; dg=g-gs[0]; H,dH=assembly(g,dg); assert np.linalg.eigvalsh(H).min()>0
    rng=np.random.default_rng(369); x=rng.normal(size=90); work=x@dH@x/2
    for step in (1e-3,1e-4):
        hp,_=assembly(g+step*dg,np.zeros_like(g)); hm,_=assembly(g-step*dg,np.zeros_like(g)); numerical=(hp-hm)/(2*step)
        err=np.max(abs(numerical-dH)); we=abs(x@numerical@x/2-work); assert err<1e-7 and we<1e-6
        print('BR277',step,'matrix derivative error',err,'fixed-cochain work error',we,'work',work,flush=True)
    assert np.linalg.norm(dH)>1e-5


def cube():
    gs,_=run(11,full=True); R=np.diag([1,1,1,1,-1]); worst=0.; magnitude=0.; count=0
    def split(g):
        r=g[...,4,4]; a=g[...,:4,4]/r[...,None];return g[...,:4,:4]-r[...,None,None]*a[..., :,None]*a[...,None,:],a,r
    def join(t):
        h,a,r=t;g=np.zeros(h.shape[:-2]+(5,5));g[...,:4,:4]=h+r[...,None,None]*a[..., :,None]*a[...,None,:];g[...,:4,4]=g[...,4,:4]=r[...,None]*a;g[...,4,4]=r;return g
    for g0,g1 in zip(gs,gs[1:]):
        delta=g1-g0; ops=[lambda g:join(split(g)),lambda g:R@g@R,lambda g:g+delta]; expected=delta-R@delta@R
        for i,j in combinations(range(3),2):
            k=3-i-j
            for p in (g0,ops[k](g0)):
                v=ops[j](ops[i](p))-ops[i](ops[j](p)); ref=expected if (i,j)==(1,2) else 0
                worst=max(worst,np.max(abs(v-ref)));count+=1
        for order in permutations(range(3)):
            p=g0
            for i in order:p=ops[i](p)
            ref=R@g0@R+(delta if order.index(1)<order.index(2) else R@delta@R);worst=max(worst,np.max(abs(p-ref)));count+=1
        magnitude=max(magnitude,np.max(abs(expected)));worst=max(worst,np.max(abs(ops[2](g0)-g1)),np.max(abs(ops[2](g0)-delta-g0)))
    assert worst<1e-12 and magnitude>0
    print('BR278 actual history',count,'face/path array checks','max defect',worst,'max retained signed residual',magnitude,flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['material','cube'],required=True);globals()[p.parse_args().part]()
