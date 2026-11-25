"""P0AG: original cubical cross Hodge and patch charge ledger.
Initial-metric/shift-jet comparator, not moving-brane or exterior solve."""
import numpy as np
import sympy as s
from itertools import product
from scipy.integrate import solve_ivp
from scipy.optimize import root
from numpy.polynomial.legendre import leggauss
import check_hopf369_p0y as y
import hopf369_dual_midpoint as z


def surface():
    ids=[j for f in z.boundary for j in f]; R=s.zeros(54,108)
    for k,j in enumerate(ids): R[k,j]=1
    B=y.E[:,ids]; assert B*R==y.E and y.Q*y.V+B*R==y.G*y.J
    assert B.rank()==26 and B[y.P.index((1,1,1)),:]==s.zeros(1,54)
    F=s.diag(*([y.Rface]*6)); assert F.rank()==24
    assert s.ones(1,27)*B==s.ones(1,54)
    # Fixed-chart discrete gauge defect is identically zero for every current.
    assert y.G*y.J-y.Q*y.V-B*R==s.zeros(27,108)
    print('surface: 54 patches, weak rank',B.rank(),'nullity',54-B.rank(),'face rank',F.rank())
    return np.array(B,float),np.array(R,float)


def assembly(eps=.25,order=3):
    sol=solve_ivp(lambda r,u:[u[1],-eps**2*64/(12*(1+r*r)**4)*u[0]],(0,64),[0,1],rtol=2e-12,atol=2e-14,dense_output=True)
    normal=sol.y[1,-1]
    def geom(x):
        r=np.linalg.norm(x); u,up=sol.sol(r); psi=(u/r if r else 1)/normal
        a=eps*z.A(x); S=1+a@a; h=psi**2*(np.eye(3)+np.outer(a,a))
        gp=(up-u/r)*x/(r*r*normal) if r else np.zeros(3)
        gs=-16*eps**2*x/(1+r*r)**3
        F=(4*eps*x[2]/(1+r*r)**2+3*a@gp/psi-a@gs/(2*S))/psi**2
        return h,F*a/S
    M=np.zeros((54,54));N=np.zeros((36,36));L=np.zeros((54,36));vol=np.zeros(33); speed=0.
    t,w=leggauss(order);t=(t+1)/2;w=w/2
    for p in z.cells:
        for ijk in product(range(order),repeat=3):
            x=t[list(ijk)]; e,b=z.basis(p,x); h,shift=geom(np.array(p)+x-1); g=np.sqrt(np.linalg.det(h)); W=g*np.linalg.inv(h); wt=np.prod(w[list(ijk)])
            M+=wt*e.T@W@e; N+=wt*b.T@(h/g)@b; L+=wt*(W@e).T@np.cross(shift,b.T).T
            speed=max(speed,np.sqrt(shift@h@shift))
    bounds=[(-1,-.5),(-.5,.5),(.5,1)]
    for i,p in enumerate(z.P):
        lo=np.array([bounds[k][0] for k in p]); width=np.array([bounds[k][1]-bounds[k][0] for k in p])
        for ijk in product(range(order),repeat=3):
            h,_=geom(lo+width*t[list(ijk)]); vol[i]+=np.prod(w[list(ijk)]*width)*np.sqrt(np.linalg.det(h))
    vol[27:]=4
    K=np.linalg.inv(M); cross=K@L; H0=np.block([[K,np.zeros((54,36))],[np.zeros((36,54)),N]]); Hs=np.block([[np.zeros((54,54)),cross],[cross.T,np.zeros((36,36))]])
    print('shift derivative cross norm',np.linalg.norm(cross),'quadrature max shift speed derivative',speed)
    assert np.linalg.norm(cross)>1e-4
    return H0,Hs,vol


def assay(H0,Hs,vol,B,R):
    S=np.block([[np.zeros((54,54)),z.C.T],[-z.C,np.zeros((36,36))]]); L=np.vstack((z.J,np.zeros((36,108)))); assert np.array_equal(S,-S.T)
    outcomes=[]
    for sign in (-1,0,1):
        dt=.05; x=np.r_[np.zeros(54),z.C@np.sin(np.arange(54))*.1]; n=np.ones((33,2))*vol[:,None]; surf=np.zeros(54); charges=np.array([1.,-1.]); energy=lambda nn,xx,H:np.sum(nn*(np.log(nn/vol[:,None])-1))+.5*xx@H@xx
        err=gauss=closure=0.; crosswork=0.
        for j in range(4):
            K0=H0+sign*j*dt*Hs; K1=H0+sign*(j+1)*dt*Hs; K=(K0+K1)/2
            assert np.linalg.eigvalsh(K1)[0]>0
            A=np.eye(90)-dt/2*S@K; free=np.linalg.solve(A,x); W=np.linalg.solve(A,dt/2*L)
            def evaluate(u):
                nn=np.exp(u.reshape(n.shape)); v=L.T@K@free
                return nn,v
            # joint material amount/port voltage solve; field eliminated exactly
            def terms(u):
                nn=np.exp(u[:n.size].reshape(n.shape)); v=u[n.size:]; c=nn/vol[:,None]; xi=v[:,None]*charges
                a=c[z.left]*z.bern(-xi); b=c[z.right]*z.bern(xi); m=.1*(a-b); i=m@charges; mid=free-W@i
                return nn,v,a,b,m,i,mid
            def residual(u):
                nn,v,a,b,m,i,mid=terms(u)
                return np.r_[(nn-n-dt*z.Vhat@m).ravel(),v-L.T@K@mid]
            sol=root(residual,np.r_[np.log(n).ravel(),L.T@K@free],options={'xtol':1e-10}); nn,v,a,b,m,i,mid=terms(sol.x)
            xn=2*mid-x; sn=surf+dt*R@i; assert nn.min()>0
            err=max(err,np.max(abs(residual(sol.x)))); gauss=max(gauss,np.max(abs(-z.G@xn[:54]-z.Q@(nn[:27]@charges)-B@sn)),np.max(abs(z.Z@xn[54:])))
            diss=dt*np.sum(m*(np.log(a)-np.log(b))); rem=np.sum(n*np.log(n/nn)-n+nn); metric=(xn@(K1-K0)@xn+x@(K1-K0)@x)/4
            closure=max(closure,abs(energy(nn,xn,K1)-energy(n,x,K0)-metric+diss+rem)); crosswork+=metric
            assert abs(sn.sum()-(nn[27:]@charges).sum())<1e-9
            x,n,surf=xn,nn,sn
        assert max(err,gauss,closure)<1e-8
        outcomes.append(x); print('sign',sign,'residual',err,'Gauss/divB',gauss,'energy',closure,'metric work',crosswork,'min concentration',np.min(n/vol[:,None]))
    diff=np.linalg.norm(outcomes[0]-outcomes[2]); assert diff>1e-5;print('opposite shift endpoint difference',diff)


if __name__=='__main__':
    B,R=surface(); H0,Hs,vol=assembly();assay(H0,Hs,vol,B,R)
