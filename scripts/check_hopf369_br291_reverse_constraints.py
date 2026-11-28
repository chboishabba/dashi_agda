"""Reverse finite G4 constraints from fixed original metric/first jets.
Adjusted sampled matter is a comparator; original continuum source is retained
as a signed residual, not silently replaced by constraint-compatible data.
"""
import argparse
import numpy as np
import check_hopf369_br283_284_g4_coupled as d
import check_hopf369_br287_289_g4_audit as audit
import check_hopf369_br290_magnetic_curl as magnetic


def initial(n):
    g,v,U,dx=magnetic.initial(n); before=U.copy(); I=np.linalg.inv(g);h,M,beta,alpha,root=d.adm(g)
    first=np.stack([v,*[audit.diff(g,i,dx) for i in range(3)]],axis=-3)
    # The normal Einstein projections have no second time derivatives.
    second=np.zeros(g.shape[:-2]+(4,4,4,4))
    for i in range(3):
        second[...,0,i+1,:,:]=second[...,i+1,0,:,:]=audit.diff(v,i,dx)
        second[...,i+1,i+1,:,:]=(np.roll(g,-1,axis=i)-2*g+np.roll(g,1,axis=i))/dx**2
        for j in range(i):second[...,i+1,j+1,:,:]=second[...,j+1,i+1,:,:]=audit.diff(audit.diff(g,i,dx),j,dx)
    independence=0.
    for p0 in np.ndindex((n-2,)*3):
        p=tuple(i+1 for i in p0); normal=-I[p][:,0]/np.sqrt(-I[p][0,0])
        def constraints(sec):
            R,_,_=audit.curvature(g[p],first[p],sec);G=R-.5*g[p]*np.sum(I[p]*R)
            return normal@G@normal/d.src.KAP,-(normal@G[:,1:])/d.src.KAP
        rho,j=constraints(second[p]); s=second[p].copy();s[0,0]=np.diag([.1,.2,-.3,.4]);r2,j2=constraints(s)
        independence=max(independence,abs(rho-r2),np.max(abs(j-j2)))
        U[p][:4]=np.r_[root[p]*(-alpha[p]*rho+beta[p]@j),root[p]*j]
    assert independence<1e-12
    _,_,_,_,margin=d.matter(g,U);sl=(slice(2,-2),)*3; correction=U[sl][...,:4]-before[sl][...,:4];err=np.max(abs(correction),axis=(0,1,2)); assert margin>0 and np.max(err)>0
    values,div=audit.audit(g,v,U,dx);assert max(values[:2])<1e-10 and div<1e-12
    print('BR291 reverse constraint initial H/M',values[:2].tolist(),'signed source correction ranges',correction.min(axis=(0,1,2)).tolist(),correction.max(axis=(0,1,2)).tolist(),'maxima',err.tolist(),'second-time independence',independence,'margin',margin,flush=True)
    return g,v,U,dx

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=7);p.add_argument('--steps',type=int,default=2);p.add_argument('--dt',type=float,default=.002);a=p.parse_args();d.initial=initial;audit.run(a.n,a.steps,a.dt)
