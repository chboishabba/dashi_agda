"""P0AE: manufactured Maxwell consistency, hanging ternary trace, moving Hopf jet.
Uses original AB incidence/refinement and AC curved Hodge assembly. Not a physical source run.
"""
from itertools import product, combinations
import numpy as np
import sympy as s
from scipy.integrate import solve_ivp
from scipy.sparse import block_diag, csr_matrix, eye
from scipy.sparse.linalg import splu, spsolve
from numpy.polynomial.legendre import leggauss
import check_hopf369_p0ab as ab
import check_hopf369_curved_refinement as ac
import hopf369_exterior as aa


def seam():
    c=ab.complex_grid(1); f=ab.complex_grid(3); _,H=ab.refine(1,c,f)
    P=[]; L=[]; counts=[]; splits=[]
    for k in range(4):
        nc,nf=len(c[0][k]),len(f[0][k]); free=[]; trace=[]
        for j,(axes,p) in enumerate(f[0][k]):
            (trace if 0 not in axes and p[0]==0 else free).append(j)
        keep=np.r_[np.arange(nc),nc+np.array(free,dtype=int)]; Lk=eye(nc+nf,dtype=np.int64,format='csr')[keep]
        entries=[(i,i,27) for i in range(nc)]+[(nc+j,nc+i,27) for i,j in enumerate(free)]
        for j in trace:
            axes,p=f[0][k][j]
            row=H[k].getrow(j)
            for col,v in zip(row.indices,row.data):
                ax,q=c[0][k][col];assert 0 not in ax and q[0]==0
                entries.append((nc+j,c[1][k][ax,(1,q[1],q[2])],int(v)))
        Pk=ab.sparse(entries,(nc+nf,len(keep)));assert ab.zero(Lk@Pk-27*eye(len(keep),dtype=np.int64,format='csr'))
        x=np.arange(nc+nf,dtype=np.int64)%11-5; r=27*x-Pk@(Lk@x)
        assert not np.any(Lk@r) and np.array_equal(Pk@(Lk@x)+r,27*x)
        P.append(Pk);L.append(Lk);counts.append(len(keep));splits.append(len(trace))
    D=[]
    for k in range(3):
        Db=block_diag((c[2][k],f[2][k]),format='csr');Dk=L[k+1]@Db@P[k]
        assert ab.zero(27*Db@P[k]-P[k+1]@Dk);D.append(Dk)
    assert all(ab.zero(D[k+1]@D[k]) for k in range(2))
    print('hanging trace dimensions',counts,'eliminated traces',splits,'exact constrained complex PASS',flush=True)


def loads(grid,n,order=5,eps=.25):
    # Same original AC metric and local cochain basis; added independent smooth loads.
    h=4/n;t,w=leggauss(order);t=(t+1)/2;w=w/2
    x=np.array(list(product(t,repeat=3)));wt=np.prod(np.array(list(product(w,repeat=3))),axis=1)*h**3
    sol=solve_ivp(lambda r,u:[u[1],-eps**2*64/(12*(1+r*r)**4)*u[0]],(0,64),[0,1],rtol=2e-12,atol=2e-14,dense_output=True)
    e=np.zeros((len(x),3,12));b=np.zeros((len(x),3,6));eo=[];bo=[]
    for i in range(3):
        tr=[a for a in range(3) if a!=i]
        for bits in product((0,1),repeat=2):
            off=[0]*3
            for a,v in zip(tr,bits):off[a]=v
            e[:,i,len(eo)]=np.prod([x[:,a] if v else 1-x[:,a] for a,v in zip(tr,bits)],axis=0)/h;eo.append(((i,),off))
    for i,j in combinations(range(3),2):
        k=3-i-j
        for v in (0,1):
            off=[0]*3;off[k]=v;b[:,k,len(bo)]=(-1)**k*(x[:,k] if v else 1-x[:,k])/h**2;bo.append(((i,j),off))
    l=[np.zeros(len(grid[0][k])) for k in (1,2)];norm=np.zeros(2)
    for _,p in grid[0][3]:
        X=h*(np.array(p)+x)-2;r=np.linalg.norm(X,axis=1);psi=np.divide(sol.sol(r)[0],r,out=np.ones_like(r),where=r!=0)/sol.y[1,-1]
        a=eps*np.array([aa.z.A(q) for q in X]);g=psi[:,None,None]**2*(np.eye(3)+a[:,:,None]*a[:,None,:]);det=np.sqrt(np.linalg.det(g))
        F=(1-X**2/4)**2;dF=-X*(1-X**2/4)
        E=np.zeros_like(X);E[:,2]=np.prod(F,axis=1)
        B=np.c_[F[:,0]*dF[:,1]*F[:,2],-dF[:,0]*F[:,1]*F[:,2],np.zeros(len(X))]
        for k,(basis,offs,metric,u) in enumerate(((e,eo,det[:,None,None]*np.linalg.inv(g),E),(b,bo,g/det[:,None,None],B))):
            local=np.einsum('qai,qab,qb,q->i',basis,metric,u,wt)
            ids=[grid[1][k+1][ax,tuple(np.array(p)+off)] for ax,off in offs]
            l[k][ids]+=local;norm[k]+=np.einsum('qa,qab,qb,q->',u,metric,u,wt)
    return l,norm


def convergence():
    results=[]
    for n in (2,4,8,12):
        grid=ab.complex_grid(n);C=grid[2][1];(M,N),_=ac.assemble(grid,n,5);(lE,lB),norm=loads(grid,n,5)
        # lambda=1, g=0; f specified by exact smooth E and curl E via weak form.
        e=spsolve((M+C.T@N@C).tocsc(),lE+C.T@lB);b=C@e
        errs=np.sqrt(np.maximum(0,[norm[0]-2*e@lE+e@(M@e),norm[1]-2*b@lB+b@(N@b)]))
        err=float(np.linalg.norm(errs));results.append(err)
        print('space',n,'h',4/n,'E,dE errors',errs.tolist(),'graph',err,flush=True)
        if n==4: temporal(M,N,C,e)
    assert all(a>b for a,b in zip(results,results[1:]))
    print('spatial observed rates',[float(np.log(a/b)/np.log(n2/n1)) for a,b,n1,n2 in zip(results,results[1:],(2,4,8),(4,8,12))],flush=True)


def temporal(M,N,C,u):
    curl=C@u;force=C.T@(N@curl)-M@u;errs=[];closures=[]
    for steps in (5,10,20,40):
        dt=1/steps;solve=splu((2*M+dt**2/2*C.T@N@C).tocsc()).solve;e=u.copy();b=np.zeros_like(curl);work=0.;U0=(e@(M@e))/2
        for j in range(steps):
            jload=np.sin((j+.5)*dt)*force
            em=solve(2*M@e+dt*(C.T@(N@b)+jload));en=2*em-e;bn=b-dt*C@em;work+=dt*em@jload;e,b=en,bn
        de=e-np.cos(1)*u;db=b+np.sin(1)*curl
        errs.append(float(np.sqrt(de@(M@de)+db@(N@db))));closures.append(abs((e@(M@e)+b@(N@b))/2-U0-work))
    rates=np.log2(np.array(errs[:-1])/errs[1:]);assert np.min(rates)>1.9 and max(closures)<1e-10
    print('temporal manufactured semidiscrete errors',errs,'rates',rates.tolist(),'max energy closure',max(closures),flush=True)


def moving_jet():
    # X6 and V4 actual initial jets in Gaussian ambient chart. Central expansion.
    x,y,z,eps,p=s.symbols('x y z eps p', real=True);r2=x*x+y*y+z*z
    # Taylor expansion to first order of shape acceleration from exact X6 expression.
    a=s.Matrix([-4*eps*y,4*eps*x,2*eps]);gp=-s.Rational(16,9)*eps**2*p*s.Matrix([x,y,z]);gS=-16*eps**2*s.Matrix([x,y,z]);S=1+4*eps**2
    acc=4*eps*z/p**2+3*a.dot(gp)/p**3-a.dot(gS)/(2*p**2*S)
    k=s.diff(acc,z);assert s.simplify(k-(4*eps-s.Rational(32,3)*eps**3+16*eps**3/S)/p**2)==0
    gamma=p**2*s.diag(1,1,S);a0=s.Matrix([0,0,2*eps]);phi2=-s.Rational(112,3)*eps**2/p
    base2=eps**2*s.diag(s.Rational(416,9),s.Rational(416,9),-s.Rational(160,9));A2=s.Matrix([0,0,-32*eps/p**2]);a2=A2+s.Matrix([0,0,k])
    h2=base2+2*p*phi2*a0*a0.T+p**2*(a2*a0.T+a0*a2.T)
    fixed2=base2+2*p*phi2*a0*a0.T+p**2*(A2*a0.T+a0*A2.T)
    assert s.simplify(h2[2,2]-fixed2[2,2]-4*eps*p**2*k)==0
    # h_0i derivative = p² f_tt a_i; at center beta_dot=0, but its derivative is nonzero.
    Dbeta=s.diag(0,0,2*eps*k/S);lie=Dbeta.T*gamma+gamma*Dbeta;Kdot=-(h2-lie)/2
    assert s.simplify(lie[2,2]-4*eps*p**2*k)==0
    assert (Kdot+fixed2/2).applyfunc(s.simplify)==s.zeros(3) # bending shift cancels spatial jet at center in Kdot
    # Fixed densitized flux metric derivative; exact stress work for the actual anisotropic jet.
    D=s.Matrix(s.symbols('D:3'));B=s.Matrix(s.symbols('B:3'));ginv=gamma.inv();tr=s.trace(ginv*h2);sqrtg=s.Symbol('sqrtg',positive=True)
    dN=(h2-tr*gamma/2)/sqrtg
    stress=((D.dot(gamma*D)+B.dot(gamma*B))*ginv/2-D*D.T-B*B.T)/sqrtg**2
    assert s.simplify((D.dot(dN*D)+B.dot(dN*B))/2+sqrtg*s.trace(stress*h2)/2)==0
    val={eps:s.Rational(1,4),p:s.Float('1.0580239940265903')}
    print('moving jet central grad f_tt',float(k.subs(val)),'induced gamma_ddot diag',[float(h2[i,i].subs(val)) for i in range(3)],'shift derivative gradient',float(Dbeta[2,2].subs(val)),'Kdot diag',[float(Kdot[i,i].subs(val)) for i in range(3)],flush=True)


if __name__=='__main__':
    seam();moving_jet();convergence()
