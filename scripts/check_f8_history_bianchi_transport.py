"""Original short-slab Fourier Bianchi diagnostic using independently differentiated history values.
Not a certified residual enclosure; no PDE substitution in the derivative oracle.
"""
import numpy as np
from scipy.special import roots_legendre
from scipy.interpolate import CubicSpline
from check_f8_characteristic_history import coefficient,evolve
from check_f8_pair_bianchi_transport import pair
from itertools import product


def history(kh,cells,t,n,h):
    z=1/np.sinh(np.arcsinh(t)-n); T=np.arcsinh(t)-np.sqrt(1+z*z)
    # inverse chart and independent local tensor-product polynomial derivative stencil
    grid=np.arange(-2,3); A=np.array([grid**i for i in range(5)],float)
    weights=np.linalg.solve(A,np.diag([1,1,2,6,24]))
    vals=np.empty((5,5,len(kh)))
    for i,j in product(range(5),repeat=2):
        zz=z+h*grid[j]; TT=T+h*grid[i]; tt=np.sinh(TT+np.sqrt(1+zz*zz)); nn=TT+np.sqrt(1+zz*zz)-np.arcsinh(1/zz)
        vals[i,j]=evolve(kh,np.ones_like(kh),cells,tt,sample_n=nn)[-1][:,0]
    jets={(i,j):np.einsum('a,b,abk->k',weights[:,i],weights[:,j],vals)/h**(i+j) for i in range(4) for j in range(4-i)}
    return z,{ij:CubicSpline(kh,v*coefficient(kh)) for ij,v in jets.items()}


def mode(k,E,interp):
    a=np.zeros((5,5),complex);a[1:4,1:4]=E; r=np.linalg.norm(k)
    d={ij:f(r) for ij,f in interp.items()}
    def scalar(ids):return d[ids.count(0),ids.count(4)]*np.prod([1j*k[i-1] for i in ids if 1<=i<=3])
    out=[scalar(())*a]
    for m in (1,2,3):
        v=np.empty((5,)*m+(5,5),complex)
        for ids in product(range(5),repeat=m):v[ids]=scalar(ids)*a
        out.append(v)
    return tuple(out)


def run(cells=128,nh=12,nodes=3,cutoff=80,k=30.,t=1.035,n=.015,h=.0005):
    kh=cutoff*(1-np.cos(np.linspace(0,np.pi,nh)))/2;z,interp=history(kh,cells,t,n,h)
    u=np.array([1.,2.,3.]);u/=np.linalg.norm(u);v=np.cross(u,[0.,0.,1.]);v/=np.linalg.norm(v);rot=np.column_stack((u,v,np.cross(u,v)));Q=rot.T@np.diag([0.,1.,-1.])@rot
    axis=np.array([k,0.,0.]);I=np.eye(3);a,w=roots_legendre(nodes)
    out=np.zeros((5,5),complex); R=np.zeros(5,complex); predicted=R.copy(); budget=0.; worst=0.
    def E(p):P=I-np.outer(p,p)/(p@p);return P@Q@P-P*np.trace(P@Q)/2
    for p,wp in zip(cutoff*(a+1)/2,w*cutoff/2):
        lo=abs(k-p);hi=min(k+p,cutoff)
        if hi<=lo:continue
        for q,wq in zip(lo+(hi-lo)*(a+1)/2,(hi-lo)*w/2):
            c=(k*k+p*p-q*q)/(2*k*p);r=p*np.sqrt(max(0.,1-c*c))
            for ph in 2*np.pi*np.arange(16)/16:
                P=np.array([p*c,r*np.cos(ph),r*np.sin(ph)]);V=axis-P
                M,D,B,_,_=pair(mode(P,E(P),interp),mode(V,E(V),interp),z)
                # pair includes both orders: half-weight on the full triangle.
                wt=wp*wq*p*q/(8*np.pi**2*k*16)
                out+=wt*M;R+=wt*D;predicted+=wt*B;budget+=wt*np.linalg.norm(B);worst=max(worst,np.linalg.norm(D-B))
    err=np.linalg.norm(R-predicted); assert np.isfinite(budget) and np.isfinite(err) and budget>0
    assert err<1e-8*max(1.,budget)
    print(dict(cells=cells,nh=nh,nodes=nodes,h=h,source=float(np.linalg.norm(out)),residual=float(np.linalg.norm(R)),off_shell_budget=budget,identity_defect=float(err),max_pair_defect=worst),flush=True)
    return out,R,predicted,budget

if __name__=='__main__':
    run();run(cells=256,nh=16,nodes=4,h=.0004)
