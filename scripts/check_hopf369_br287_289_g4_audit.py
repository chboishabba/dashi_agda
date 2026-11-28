"""Independent source-matched G4 curvature and signed worldtube balance.
Finite diagnostics, not a stability or continuum certificate.
"""
import argparse, inspect
import numpy as np
import check_hopf369_br283_284_g4_coupled as d
from check_hopf369_br242_244_constraint_history import curvature as curvature5

# Reuse the independent pointwise contraction, not the evolution einsums.
ns=dict(np=np)
exec(inspect.getsource(curvature5).replace('range(5)','range(4)').replace('(5,5,5,5)','(4,4,4,4)').replace('(5,5,5)','(4,4,4)').replace('(5,5)','(4,4)').replace('zeros(5)','zeros(4)'),ns)
curvature=ns['curvature']

def diff(x,i,dx):return (np.roll(x,-1,axis=i)-np.roll(x,1,axis=i))/(2*dx)

def audit(g,v,U,dx):
    T,up,F,den,margin=d.matter(g,U); I=np.linalg.inv(g); tr=np.sum(I*T,axis=(-2,-1)); a=d.acc(g,v,dx)-2*d.src.KAP*(T-.5*g*tr[...,None,None])/I[...,0,0,None,None]
    first=np.stack([v,*[diff(g,i,dx) for i in range(3)]],axis=-3)
    m=g.shape[0]//2; pts=[(m,m,m),(m+1,m,m),(m,m-1,m),(m,m,m+1)]
    values=np.zeros(5)
    for p in pts:
        sec=np.zeros((4,4,4,4));sec[0,0]=a[p]
        for i in range(3):
            sec[0,i+1]=sec[i+1,0]=diff(v,i,dx)[p]
            sec[i+1,i+1]=((np.roll(g,-1,axis=i)-2*g+np.roll(g,1,axis=i))/dx**2)[p]
            for j in range(i):sec[i+1,j+1]=sec[j+1,i+1]=diff(diff(g,i,dx),j,dx)[p]
        R,C,DC=curvature(g[p],first[p],sec); normal=-I[p][:,0]/np.sqrt(-I[p][0,0]); E=R-.5*g[p]*np.sum(I[p]*R)-d.src.KAP*T[p]
        reduced=R-(DC+DC.T)/2-d.src.KAP*(T[p]-.5*g[p]*tr[p]);
        values=np.maximum(values,[abs(2*normal@E@normal),np.max(abs(normal@E[:,1:])),np.max(abs(C)),np.max(abs(reduced)),np.max(abs(R-R.T))])
    assert values[3]<1e-10 and values[4]<1e-10
    sl=(slice(2,-2),)*3; b=sum(diff(U[...,4+i],i,dx) for i in range(3)); return values,float(np.max(abs(b[sl])))

def run(n,steps,dt):
    history=[]; midpoints=[]
    def capture(g,v,U,dx):history.append((g.copy(),v.copy(),U.copy(),dx))
    def mid(g,v,U,dx):midpoints.append((g.copy(),v.copy(),U.copy(),dx))
    source=inspect.getsource(d.run).replace('    b0=divB(U);','    capture(g,v,U,dx)\n    b0=divB(U);').replace('old=U.copy();','mid(g+dt*w/2,v+dt*a/2,U+dt*b/2,dx);old=U.copy();').replace('margin=min(margin,m,mm);','capture(g,v,U,dx);margin=min(margin,m,mm);')
    ns=dict(vars(d),capture=capture,mid=mid);exec(source,ns);ns['run'](n,steps,dt)
    initial,b0=audit(*history[0]); final,b1=audit(*history[-1]);print('BR287 curvature initial/final [H,M,C,reduced,symmetry]',initial.tolist(),final.tolist(),'absolute magnetic divergence',b0,b1,flush=True)
    sl=(slice(2,-2),)*3; total=np.zeros(4); work=np.zeros(4); flux=np.zeros(4); local=0.
    for old,new,midpoint in zip(history,history[1:],midpoints):
        g,v,U,dx=midpoint;T,up,F,den,_=d.matter(g,U);first=np.stack([v,*[diff(g,i,dx) for i in range(3)]],axis=-3);src=.5*den[...,None]*np.einsum('...ij,...kij->...k',up,first)
        change=(new[2]-old[2])[sl][...,:4]; local=max(local,float(np.max(abs(change/dt+sum(diff(F[...,i,:4],i,dx)[sl] for i in range(3))-src[sl])))); total+=change.sum(axis=(0,1,2))*dx**3;work+=dt*src[sl].sum(axis=(0,1,2))*dx**3
        for i in range(3):
            f=np.moveaxis(F[...,i,:4],i,0);face=f[-2,2:-2,2:-2]+f[-3,2:-2,2:-2]-f[1,2:-2,2:-2]-f[2,2:-2,2:-2];flux+=dt*dx**2*face.sum(axis=(0,1))/2
    ledger=np.max(abs(total+flux-work));assert ledger<1e-10 and local<1e-10
    print('BR288 signed worldtube delta/flux/source',total.tolist(),flux.tolist(),work.tolist(),'ledger',ledger,'local midpoint',local,flush=True)
    # Independent endpoint trapezoidal stress balance, not same-stage RHS replay.
    defect=0.
    for old,new in zip(history,history[1:]):
        terms=[]
        for g,v,U,dx in (old,new):
            T,up,F,den,_=d.matter(g,U);first=np.stack([v,*[diff(g,i,dx) for i in range(3)]],axis=-3);src=.5*den[...,None]*np.einsum('...ij,...kij->...k',up,first);terms.append(sum(diff(F[...,i,:4],i,dx) for i in range(3))-src)
        res=((new[2]-old[2])[...,:4]/dt+(terms[0]+terms[1])/2)[sl];defect=max(defect,float(np.max(abs(res))))
    assert np.isfinite(defect);print('BR289 independent endpoint stress-balance defect',defect,flush=True)

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--n',type=int,default=7);p.add_argument('--steps',type=int,default=2);p.add_argument('--dt',type=float,default=.002);a=p.parse_args();run(a.n,a.steps,a.dt)
