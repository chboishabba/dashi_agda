"""P0AD refined physical current: exact rational geometry, finite curved fixture."""
from itertools import product
import numpy as np
import sympy as s
from scipy.sparse import csr_matrix
from scipy.sparse.linalg import splu
from scipy.optimize import root
import check_hopf369_p0y as y
import hopf369_dual_midpoint as z
import hopf369_exterior as aa
import check_hopf369_p0ab as ab
import check_hopf369_curved_refinement as ac

def hat(x,n,i):
    if x==n[i]:return s.S.One
    if i and n[i-1]<=x<n[i]:return (x-n[i-1])/(n[i]-n[i-1])
    if i+1<len(n) and n[i]<x<=n[i+1]:return (n[i+1]-x)/(n[i+1]-n[i])
    return s.S.Zero

def integ(n,i,a,b):
    p=[a]+[x for x in n if a<x<b]+[b]
    return sum((v-u)*(hat(u,n,i)+hat(v,n,i))/2 for u,v in zip(p,p[1:]))

def loads(grid,H):
    d=list(map(s.Rational,[-1,-.5,.5,1]));f=[s.Rational(i,3)-1 for i in range(7)]
    T=s.Matrix(7,3,lambda i,j:integ(f,i,d[j],d[j+1])/(d[j+1]-d[j]))
    L=s.Matrix(6,4,lambda i,j:3*integ(d,j,f[i],f[i+1]))
    E=s.zeros(7,4);E[0,0]=-1;E[6,3]=1;D=s.zeros(6,7)
    for i in range(6):D[i,i]=-1;D[i,i+1]=1
    assert D.T*L-E==T*y.H and T.rank()==3 and L.rank()==4 and s.ones(1,7)*T==s.ones(1,3)
    F=s.Matrix(6,3,lambda i,j:max(0,min(f[i+1],d[j+1])-max(f[i],d[j]))/(d[j+1]-d[j]))
    RF=s.kronecker_product(F,F);assert RF.rank()==9 and s.ones(1,36)*RF==s.ones(1,9)
    S=(RF.T*RF).inv()*RF.T;assert S*RF==s.eye(9)
    U=s.Matrix([[1,1,1,0,0,0],[0,0,0,1,1,1]])
    assert s.kronecker_product(U,U)*RF==y.Rface
    den=int(s.ilcm(*[a.q for a in list(T)+list(L)+list(E)]));scale=den**3
    t,l,e=(np.array(a*den,dtype=np.int64) for a in (T,L,E))
    Q=np.zeros((len(grid[0][0]),27),np.int64);J=np.zeros((len(grid[0][1]),108),np.int64);B=np.zeros((len(grid[0][0]),108),np.int64)
    for p in product(range(7),repeat=3):
        row=grid[1][0][(),tuple(v+3 for v in p)]
        for j,q in enumerate(y.P):Q[row,j]=np.prod([t[p[a],q[a]] for a in range(3)])
        for j,(a,q) in enumerate(y.flux):B[row,j]=(-1 if q[a]==0 else 1)*e[p[a],q[a]]*np.prod([t[p[b],q[b]] for b in range(3) if b!=a])
    for a in range(3):
        for p in product(*[range(6 if b==a else 7) for b in range(3)]):
            row=grid[1][1][(a,),tuple(v+3 for v in p)]
            for j,(b,q) in enumerate(y.flux):
                if a==b:J[row,j]=(-1 if q[a]==0 else 1)*l[p[a],q[a]]*np.prod([t[p[k],q[k]] for k in range(3) if k!=a])
    Q,J,B=map(csr_matrix,(Q,J,B));G=grid[2][0].T;V=np.array(y.V,dtype=np.int64)
    assert np.array_equal((G@J-B).toarray(),Q@V)
    assert np.array_equal(np.asarray(Q.sum(axis=0)).ravel(),np.full(27,scale))
    for k,a,old in ((0,Q,aa.Q),(1,J,aa.J),(0,B,aa.B)):
        assert np.array_equal((H[k].T@a).toarray(),np.rint(27*scale*old).astype(np.int64))
    print('exact loads',Q.shape,J.shape,B.shape,'denominator',scale,'fine face rank',RF.rank(),flush=True)
    return Q.astype(float)/scale,J.astype(float)/scale,B.astype(float)/scale,np.array(RF,float),np.array(S,float)

def assay():
    coarse=ab.complex_grid(4);fine=ab.complex_grid(12);R,H=ab.refine(4,coarse,fine)
    Q,J,B,RF,SF=loads(fine,H);G=fine[2][0].T;C=fine[2][1];Z=fine[2][2]
    (M,N),_=ac.assemble(fine,12,3);geom=aa.assemble(order=3);vol=geom[6];dt=.08
    fac=splu((2*M+dt**2/2*C.T@N@C).tocsc());X=fac.solve(dt*J.toarray());A=J.T@X
    pot=H[1]@geom[-1]/27;pot[fine[1][1][((1,),(10,1,1))]]+=.5
    bstart=C@pot;records=[];endpoints=[]
    for ns,steps,mobility in ((3,4,0.),(3,4,.08),(29,1,.04)):
        if ns==3:
            val=np.array([1,-1,0]);A0=np.array([[1,1,0]]);A1=np.array([[0,0,1]]);weights=np.array([[1,0],[0,1],[1,1]])
        else:
            val=np.repeat(np.arange(15)%3-1,2)[:ns];val[-1]=-val[:-1].sum();A0=np.eye(ns)[0:24:2];A1=np.eye(ns)[1:24:2];weights=np.repeat(np.eye(15),2,axis=0)[:ns]
        nu=A1-A0;assert np.all(nu@val==0);k=np.full((108,ns),mobility)
        n=np.ones((33,ns))*vol[:,None];inv=n.sum(axis=0)@weights;e=np.zeros(M.shape[0]);b=bstart.copy();q=np.zeros(Q.shape[0]);size=n.size
        energy=lambda n,e,b:np.sum(n*(np.log(n/vol[:,None])-1))+.5*(e@(M@e)+b@(N@b))
        for t in range(steps):
            free=fac.solve(2*M@e+dt*C.T@(N@b));vf=J.T@free
            def terms(nn,v):
                c=nn/vol[:,None];xi=v[:,None]*val;a=c[z.left]*z.bern(-xi);bb=c[z.right]*z.bern(xi);mol=k*(a-bb);cur=mol@val
                rates=.04*(np.exp(np.log(c[:27])@A0.T)-np.exp(np.log(c[:27])@A1.T));f=z.Vhat@mol;f[:27]+=vol[:27,None]*(rates@nu)
                return f,cur,a,bb,mol,rates
            def unpack(u):return np.exp(np.clip(u[:size],-60,60)).reshape(n.shape),u[size:]
            def residual(u):
                nn,v=unpack(u);f,cur,*_=terms(nn,v);return np.r_[(nn-n-dt*f).ravel(),v-vf+A@cur]
            sol=root(residual,np.r_[np.log(n).ravel(),vf],options={'xtol':1e-10});assert np.all(np.isfinite(sol.x)) and np.max(abs(sol.x[:size]))<59
            nn,v=unpack(sol.x);f,cur,a,bb,mol,rates=terms(nn,v);em=free-X@cur;ee=2*em-e;bn=b-dt*C@em;qn=q+dt*B@cur
            rn=nn-n-dt*f;rd=M@(ee-e)-dt*(C.T@(N@((bn+b)/2))-J@cur);rv=v-J.T@em
            g=-G@(M@ee)-Q@(nn[:27]@val)-qn;g0=-G@(M@e)-Q@(n[:27]@val)-q
            prop=np.max(abs(g-g0+G@rd+Q@(rn[:27]@val)))
            mu=np.log(nn/vol[:,None]);Dt=dt*np.sum(mol*(np.log(a)-np.log(bb)));Dr=-dt*np.sum(vol[:27,None]*rates*(mu[:27]@nu.T));Bc=np.sum(n*np.log(n/nn)-n+nn)
            transfer=dt*em@(J@cur);workdef=dt*rv@cur;delta=energy(nn,ee,bn)-energy(n,e,b);closure=delta+Dt+Dr+Bc-(np.sum(mu*rn)+em@rd)-workdef
            err=max(np.max(abs(rn)),np.max(abs(rd)),np.max(abs(rv)));assert err<1e-9
            assert max(abs(closure),prop,np.max(abs(g)),np.max(abs(Z@(bn-b))),abs(qn.sum()-np.sum(nn[27:]@val)),np.max(abs(nn.sum(axis=0)@weights-inv)))<1e-8
            assert min(Dt,Dr,Bc)>-1e-9
            raw=np.array([dt*mol[ix] for ix in z.boundary]);ff=np.array([RF@u for u in raw]);assert np.max(abs(raw-np.array([SF@u for u in ff])))<1e-12
            records.append(dict(error=err,closure=closure,gauss=np.max(abs(g)),prop=prop,minimum=np.min(nn/vol[:,None]),workdef=workdef,transfer=transfer,delta=delta,forward=dt*k*a,backward=dt*k*bb,flux=dt*mol,weak_boundary=qn.copy(),fine_face=ff,coarse_face=np.array([z.Rface@u for u in raw]),coarse_complement=np.array([u-z.Sface@(z.Rface@u) for u in raw]),voltage=v.copy(),amount_residual=rn,displacement_residual=rd,voltage_residual=rv,gauss_residual=g))
            n,e,b,q=nn,ee,bn,qn
        endpoints.append(e);print('trajectory',ns,steps,mobility,'delta',sum(r['delta'] for r in records[-steps:]),'ionic work',sum(r['transfer'] for r in records[-steps:]),flush=True)
    print('steps',len(records),'mobile/frozen coarse electric difference',np.linalg.norm(R[1]@(endpoints[1]-endpoints[0])),flush=True)
    for k in ('error','closure','gauss','prop','minimum','workdef'):print(k,max(abs(r[k]) for r in records),min(r[k] for r in records))
    return records

if __name__=='__main__':assay()
