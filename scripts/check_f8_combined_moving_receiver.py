"""Native two-step moving-mask receiver and shared-clock regression.
Finite diagnostic only; masks fixed with respect to source amplitude.
"""
import numpy as np
from scipy.optimize import brentq
from ksw668_f8_tt_multipole import stage,F
from ksw668_f8_fv_source_flux import exact_cell_averages
from warp_frame_attribution import project,metric,raise_dual,lower,native_reverse
from warp_native_geometric_receiver import receiver_bank
from warp_israel_affine import radial_source_at_receiver,offsets,forced_identity

def check(order):
    dr,dy,h,eps=.008,.012,.001,.04
    nr,ny=13,7; rx=.025; shape=(3,3,ny,nr)
    src=exact_cell_averages(eps,np.arange(nr)*dr,dr)
    ts=np.array([brentq(lambda t:F(t)-F(1)-.02-k*h/2,.5,3) for k in range(5)])
    b=1/ts; v=-1/np.sqrt(1+ts**2)
    inc=np.array([[0,2,1],[2,4,3]])
    cp=np.zeros((3,nr));cm=cp.copy()
    for q,d in enumerate((3,7,11)):
        j=np.arange(1,nr);den=(j+.5)**d-(j-.5)**d
        cp[q,1:]=d*(j+.5)**(d-1)/den
        cm[q,1:]=d*(j-.5)**(d-1)/den
    def geo(k):return b[k],v[k]
    def W(k):return metric(ny,nr,dr,dy,b[k])
    def euler(x,k,f=0.):
        out=np.empty_like(x)
        stage(*x,*out,dr,dy,*geo(k),f,src,cp,cm,order)
        return project(x+h*out)
    units=[euler(np.zeros(shape),k,1.) for k in range(5)]
    obs=receiver_bank(ts[2],rx,eps,dr,dy,h,v,1,nr,ny)
    dg=radial_source_at_receiver(src,1.,rx,eps,dr)
    D=offsets(dg)
    threshold=2*dy+(b[0]+b[4])/2
    masks=(b[:,None]+dy*np.arange(ny)[None,:]<threshold)[:,None,None,:,None]
    assert np.any(masks[0]!=masks[4])
    rng=np.random.default_rng(1530+order)
    x0=project(rng.normal(size=shape)*1e-4)
    f=np.array([.013,-.021,.034,-.012,.018])
    def pair(a,b):return np.sum(a*b,axis=(0,2,3))
    def close(a,b):
        np.testing.assert_allclose(a,b,rtol=1e-9,atol=1e-9)
    def step(x,ks,r):
        a,b0,c=ks
        u=euler(x,a)+r[0]
        z=.75*x+.25*(euler(u,b0)+r[1])
        return u,z,x/3+2*(euler(z,c)+r[2])/3
    def full(f,collapse=False):
        x=x0.copy(); states=[x]; stages=[]
        for i,ks in enumerate(inc):
            r=[f[k]*units[k] for k in ks]
            u,z,y=step(x,ks,r)
            if collapse and i==1:
                # Wrong identification: B0 input is A1 input.
                u=euler(stages[0][0],ks[0])+r[0]
                z=.75*x+.25*(euler(u,ks[1])+r[1])
                y=x/3+2*(euler(z,ks[2])+r[2])/3
            stages.append((u,z));states.append(y);x=y
        return states,stages
    def read(states):
        return np.array([sum(pair(o,x) for o,x in zip(ch,states)) for ch in obs])
    def adjoint(rows):
        p=np.array([project(ch[2]) for ch in rows])
        ps=[None,None,p.copy()]
        grad=np.zeros((6,2,3,3))
        for i in (1,0):
            k=2*i;ks=inc[i];prev=[]
            for ch in range(6):
                adj,dual=native_reverse(raise_dual(p[ch],W(k+2)),W(k),W(k+2),
                    dr,dy,h,tuple(geo(j) for j in ks),order)
                for j,(d,l) in enumerate(zip(dual,ks)):
                    grad[ch,i,j]=pair(d,units[l])
                prev.append(lower(adj,W(k))+project(rows[ch,i]))
            p=np.array(prev);ps[i]=p.copy()
        return ps,grad
    def aggregate(grad,direct):
        g=np.zeros((6,5,3));g[:,2]=direct
        for i in range(2):
            for j in range(3):g[:,inc[i,j]]+=grad[:,i,j]
        return g
    def regional(f,m):
        xs,stages=full(f)
        zs=[m[0]*xs[0]]; terms=[]
        for i,ks in enumerate(inc):
            a,b0,c=ks;x=xs[i];u,z=stages[i]
            q0,qa,qb,q1=m[a],m[b0],m[c],m[b0]
            A=lambda x:euler(x,a)
            B=lambda x:euler(x,b0)
            C=lambda x:euler(x,c)
            ka=qa*A(x)-A(q0*x)
            kb=qb*B(u)-B(qa*u)
            kc=q1*C(z)-C(qb*z)
            t=np.array([C(B(ka))/6,C(kb)/6,2*kc/3,
                        C((qb-q0)*x)/2,(q1-q0)*x/3])
            r=[q*f[k]*units[k] for q,k in zip((qa,qb,q1),ks)]
            _,_,y=step(zs[-1],ks,r)
            e=q0*x-zs[-1]
            transported=step(e,ks,[np.zeros(shape)]*3)[2]
            close(q1*xs[i+1]-y,transported+t.sum(0))
            zs.append(y);terms.append(t)
        # Wall observation owns the affine offset once; not per stage.
        direct=D*int(m[2,0,0,0,0])
        target=read([m[2*i]*x for i,x in enumerate(xs)])+f[2]*direct
        base=read(zs)+f[2]*direct
        ps,_=adjoint(obs)
        ledger=np.array([[np.array([pair(p,t) for p in ps[i+1]])
                          for t in terms[i]] for i in range(2)])
        close(target-base,ledger.sum(axis=(0,1)))
        _,g=adjoint(obs*m[::2][None,...])
        return target,base,np.array(terms),ledger,aggregate(g,direct)
    # Cast masks to floats: differences are signed, not Boolean subtraction.
    m=masks.astype(float)
    a=regional(f,m);c=regional(f,1-m)
    xs,_=full(f);whole=read(xs)+f[2]*D
    close(a[0]+c[0],whole);close(a[1]+c[1],whole)
    close(a[2]+c[2],0);close(a[3]+c[3],0)
    ps,sg=adjoint(obs);g=aggregate(sg,D)
    close(a[4]+c[4],g)
    delta=.001
    def response(f):return read(full(f)[0])+f[2]*D
    def fd(fun):
        return np.stack([(fun(f+delta*z)-fun(f-delta*z))/(2*delta)
                         for z in np.eye(5)],axis=1)
    close(fd(response),g)
    close(fd(lambda f:regional(f,m)[0]),a[4])
    close(fd(lambda f:regional(f,1-m)[0]),c[4])
    def rejects(name,x,y):
        if np.allclose(x,y,rtol=1e-9,atol=1e-9):
            raise AssertionError('undetected mutation: '+name)
    for i,j in ((0,1),(1,0)):
        bad=sg.copy();bad[:,i,j]=0
        rejects('omitted shared incidence',aggregate(bad,D),g)
    rejects('duplicate direct offset',aggregate(sg,2*D),g)
    rejects('collapsed stage state',read(full(f,True)[0]),read(xs))
    rejects('omitted carries',a[3][:,:3].sum(axis=(0,1)),a[3].sum(axis=(0,1)))
    rejects('duplicate regional offset',a[0]+c[0]+f[2]*D,whole)
    # Independent wall trace from native U and characteristic P,M.
    x=xs[1];ir=int(rx/dr);idx=np.arange(ir-1,ir+3)
    w=np.linalg.solve((idx-rx/dr)[None,:]**np.arange(4)[:,None],[1.,0.,0.,0.])
    fac=(rx/eps)**np.arange(0,6,2)
    dstrong=fac*(((-3*x[0,:,0,:]+4*x[0,:,1,:]-x[0,:,2,:])/(2*dy))[:,idx]@w)
    P=fac*(x[1,:,0,:][:,idx]@w);M=fac*(x[2,:,0,:][:,idx]@w)
    A=((1+v[2])*P+(1-v[2])*M)/2
    dc=(P-M)/2;coef=1-v[2]**2
    fc=v[2]*A+coef*dc-f[2]*dg
    fs=v[2]*A+coef*dstrong-f[2]*dg
    close(fs,whole[4]);close(fs,fc+coef*(dstrong-dc))
    rejects('characteristic substituted for strong trace',fc,fs)
    err,scale=forced_identity(whole,f[2]*dg,ts[2])
    assert np.all(np.abs(err)<=1e-10*np.maximum(1.,scale))
    print('PASS order',order,'combined ledger, gradient, complements, seven mutations',
          'max trace defect',np.max(np.abs(fs-fc)),flush=True)

if __name__=='__main__':
    for order in (3,4):check(order)
