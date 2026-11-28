"""Match BR256 diagonal second jets and independently audit covector coefficients."""
import argparse
import inspect
import numpy as np
import check_hopf369_br257_259_subsidiary_evolution as donor
from check_hopf369_br256_spatial import operators,diff,second
from check_hopf369_br242_244_constraint_history import curvature

def matched():
    ns=dict(vars(donor),second=second)
    old='for j in range(1,4):h[...,i,j,:,:]=diff(f[...,j,:,:],dx,i-1)'
    new='for j in range(1,4):h[...,i,j,:,:]=second(g,dx,i-1) if i==j else diff(f[...,j,:,:],dx,i-1)'
    src=inspect.getsource(donor.geometry);assert src.count(old)==1
    exec(src.replace(old,new),ns);return ns['geometry']

def audit():
    init,acc=operators(4);g,v,dx=init(11)
    rng=np.random.default_rng(369);w=rng.normal(size=v.shape)*.01;v+=(w+w.swapaxes(-1,-2))/2;a=acc(g,v,dx)
    m=matched()(g,v,a,dx);o=donor.geometry(g,v,a,dx);sl=(slice(2,-2),)*3
    err=np.max(abs(m['E'][sl]));old=np.max(abs(o['E'][sl]));assert err<1e-11 and old>1e-4
    print('BR260 matched reduced defect',err,'old composed defect',old,flush=True)
    worst=np.zeros(3)
    for p in [(5,5,5),(6,4,6),(4,6,5)]:
        f=np.zeros((5,5,5));h=np.zeros((5,5,5,5));f[0]=v[p];h[0,0]=a[p]
        for i in range(1,4):
            f[i]=diff(g,dx,i-1)[p];h[0,i]=h[i,0]=diff(v,dx,i-1)[p]
            for j in range(1,4):h[i,j]=second(g,dx,i-1)[p] if i==j else diff(diff(g,dx,j-1),dx,i-1)[p]
        h=(h+h.swapaxes(0,1))/2;gg=g[p];I=np.linalg.inv(gg);den=np.sqrt(-np.linalg.det(gg));R,C,U=curvature(gg,f,h)
        G=np.zeros((5,5,5));DG=np.zeros((5,5,5,5));N=range(5)
        for k in N:
            for b in N:
                for c in N:
                    G[k,b,c]=sum(I[k,e]*(f[b,e,c]+f[c,e,b]-f[e,b,c])/2 for e in N)
                    for l in N:DG[l,k,b,c]=sum(I[k,e]*(h[l,b,e,c]+h[l,c,e,b]-h[l,e,b,c])/2 for e in N)
        for l in N:
            for k in N:
                for b in N:
                    for c in N:DG[l,k,b,c]-=sum(I[k,r]*f[l,r,e]*G[e,b,c] for r in N for e in N)
        T=np.zeros((5,5,5));Z=np.zeros((5,5))
        for b in N:
            for i in N:
                for c in N:T[b,i,c]=-2*den*sum(I[a0,b]*G[c,a0,i] for a0 in N)
        for i in N:
            for c in N:Z[i,c]=den*(sum(I[a0,b]*(-DG[a0,c,b,i]+sum(G[d,a0,b]*G[c,d,i]+G[d,a0,i]*G[c,b,d] for d in N)) for a0 in N for b in N)+sum(R[i,d]*I[d,c] for d in N))
        worst=np.maximum(worst,[np.max(abs(T-m['T'][p])),np.max(abs(Z-m['Z'][p])),np.max(abs(R-(U+U.T)/2-m['E'][p]))])
    assert max(worst)<1e-11,worst
    print('BR261 independent T,Z,E contraction errors',worst.tolist(),flush=True)

def evolve(n,steps):
    ns=dict(vars(donor),geometry=matched());exec(inspect.getsource(donor.run),ns);ns['run'](n,steps)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['audit','evolve'],required=True);p.add_argument('--n',type=int,default=11);p.add_argument('--steps',type=int,default=8);a=p.parse_args();audit() if a.part=='audit' else evolve(a.n,a.steps)
