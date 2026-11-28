"""Complete normalized real-time port model; numerical orbit regression, not physical law."""
import numpy as np
import sympy as S
from solar_steelman_boundary_weld import branch
from solar_steelman_carrier_mediator import OMEGA

def build(m,a):
    def arr(x):return np.array(x,dtype=float)
    def cx(x):return np.array(x,dtype=complex).ravel()
    d=m['d']; M,N,C,B,H=map(arr,(d['M'],d['N'],d['C'],m['B'],m['H']))
    T=arr(d['T']);ts=T[:1];tr=T[8:15];hi,lo=a['rows']; R=float(lo['load'])
    Ls,Ks=map(arr,branch(S.Integer(2),S.Integer(1),-hi['X'][:1,:1]));Lr,Kr=map(arr,branch(S.Integer(1),S.Integer(2),-lo['X'][8:15,8:15]))
    Mi=np.linalg.inv(M);Hi=np.linalg.inv(H)/2;Li=[np.linalg.inv(Ls),np.linalg.inv(Lr)]
    models=[(ids,{w:cx(r[w][0]+S.I*r[w][1]) for w in (1,2)},{k:complex(v) for k,v in c.items()}) for ids,r,c in a['models']]
    edges=[(a['parent'][j],j,float(a['flows'][j])) for j in a['order'][1:]];n=len(models);h=(1+1j)/np.sqrt(2)
    sizes=[len(M),len(N),len(H),1,1,1,1,7,7,7,7,n,n,n,n,n]; cuts=np.cumsum(sizes)[:-1]
    def unpack(y):return np.split(y,cuts)
    def pack(*v):return np.concatenate([np.asarray(x).ravel() for x in v])
    def store(c,u):return sum(v*u**k for k,v in c.items()).real
    def rhs(t,y,gamma=0):
        E,b,z,i,q,x,v,j,Q,X,V,e0,e1,th0,th1,p=unpack(y)
        u=np.exp(1j*(th1-th0));e=e0+e1;ratio=np.array([e[k]/store(c,u[k]) for k,(_,_,c) in enumerate(models)])
        F=np.zeros_like(z);de=np.zeros(n);dp=np.zeros(n)
        for k,(ids,r,c) in enumerate(models):
            f=np.sqrt(2)*(r[2]*u[k]**2+h*r[1]*u[k]).real*ratio[k];F[ids]+=f;de[k]-=z[ids]@f
        for k,l,flow in edges:
            f=flow*ratio[k]*ratio[l];de[k]-=f;de[l]+=f
            torque=np.imag(u[l]*u[k].conjugate())+gamma*(p[l]-p[k]);dp[k]+=torque;dp[l]-=torque
        s=np.sqrt(2)*np.cos(2*t)
        return pack(Mi@(C.T@N@b-B@z+ts.T@i-tr.T@j),-C@E,Hi@(B.T@E+F),Li[0]@(2*s-i-ts@E-Ks@q-x),i,i-v,x,Li[1]@(tr@E-R*j-Kr@Q-X),j,j-4*V,X,de*e0/e,de*e1/e,np.full(n,float(OMEGA)),float(OMEGA)+1+p,dp)
    def energy_rate(y,dy):
        E,b,z,i,q,x,v,j,Q,X,V,e0,e1,th0,th1,p=unpack(y);dE,db,dz,di,dq,dx,dv,dj,dQ,dX,dV,de0,de1,dt0,dt1,dp=unpack(dy)
        return E@M@dE+b@N@db+2*z@H@dz+i@Ls@di+q@Ks@dq+x@dx+v@dv+j@Lr@dj+Q@Kr@dQ+X@dX+4*V@dV+sum(de0+de1)+p@dp+sum(np.sin((th1[l]-th0[l])-(th1[k]-th0[k]))*((dt1[l]-dt0[l])-(dt1[k]-dt0[k])) for k,l,_ in edges)
    def orbit(t,derivative=False):
        u=np.exp(1j*t);f=lambda w,x:np.sqrt(2)*np.real(cx(x)*u**w*(h if w==1 else 1)*((1j*w) if derivative else 1))
        E=f(2,hi['E'])+f(1,lo['E']);b=f(2,hi['b'])+f(1,lo['b']);z=sum(f(w,a['data'][w][0][0]+S.I*a['data'][w][0][1]) for w in (1,2))
        ih=S.ones(1,1);il=lo['p'];bh=-lo['v'][:1,:];bl=hi['v'][8:15,:]
        def states(w,v,current,blocked):
            x=S.I*w*current/(v*v-w*w);return [f(w,current),f(w,current/(S.I*w)),f(w,x)+f(v,blocked),f(w,x/(S.I*w))+f(v,blocked/(S.I*v))]
        es=np.array([sum((1j*k if derivative else 1)*v*u**k for k,v in c.items()).real/2 for _,_,c in models]);om=float(OMEGA)
        return pack(E,b,z,*states(2,1,ih,bh),*states(1,2,il,bl),es,es,np.full(n,om if derivative else om*t),np.full(n,om+1 if derivative else (om+1)*t),np.zeros(n))
    def power(t,y,gamma):
        _,_,_,i,_,_,_,j,_,_,_,_,_,_,_,p=unpack(y);s=np.sqrt(2)*np.cos(2*t)
        return s*s-(s-i[0])**2-R*(j@j)-gamma*sum((p[l]-p[k])**2 for k,l,_ in edges)
    return rhs,orbit,energy_rate,power

def certify(m,a):
    rhs,orbit,rate,power=build(m,a);rng=np.random.default_rng(369);worst=0;ledger=0
    for t in np.linspace(0,2*np.pi,33):
        y=orbit(t);dy=rhs(t,y);ref=orbit(t,True);err=np.linalg.norm(dy-ref,np.inf)/max(1,np.linalg.norm(ref,np.inf));worst=max(worst,err)
        yp=y+.001*rng.normal(size=len(y));dyp=rhs(t,yp,.5);ledger=max(ledger,abs(rate(yp,dyp)-power(t,yp,.5)))
    print('state dimension',len(y),'relative orbit residual',worst,'perturbed energy absolute residual',ledger,flush=True)
    assert worst<1e-8 and ledger<1e-6
    print('PASS numerical full real-time RHS orbit and energy regression; no integration or full stability claim',flush=True)
if __name__=='__main__':
    import pickle
    from solar_steelman_material_metric import run as metric
    from solar_steelman_autonomous_mediator import run as mediator
    m=metric();certify(m,mediator(m))
