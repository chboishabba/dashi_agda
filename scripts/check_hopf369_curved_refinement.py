"""P0AC curved uniform refinement on the original P0AA initial metric."""
import numpy as np
from itertools import product, combinations
from scipy.integrate import solve_ivp
from scipy.sparse import coo_matrix
from scipy.sparse.linalg import spsolve
from numpy.polynomial.legendre import leggauss
import hopf369_exterior as aa
import check_hopf369_p0ab as ab

def assemble(grid,n,order,eps=.25):
    h=4/n; t,w=leggauss(order); t=(t+1)/2; w=w/2
    x=np.array(list(product(t,repeat=3))); wt=np.prod(np.array(list(product(w,repeat=3))),axis=1)*h**3
    sol=solve_ivp(lambda r,u:[u[1],-eps**2*64/(12*(1+r*r)**4)*u[0]],(0,64),[0,1],rtol=2e-12,atol=2e-14,dense_output=True)
    # Original normalized unit cochain bases; physical 1/h and 1/h^2 factors.
    e=np.zeros((len(x),3,12)); b=np.zeros((len(x),3,6)); eo=[];bo=[]
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
    entries=[[],[]]; minima=[np.inf,np.inf]
    for _,p in grid[0][3]:
        X=h*(np.array(p)+x)-2;r=np.linalg.norm(X,axis=1);u=sol.sol(r)[0];psi=np.divide(u,r,out=np.ones_like(r),where=r!=0)/sol.y[1,-1]
        a=eps*np.array([aa.z.A(q) for q in X]);g=psi[:,None,None]**2*(np.eye(3)+a[:,:,None]*a[:,None,:]);det=np.sqrt(np.linalg.det(g))
        for k,(basis,offs,metric) in enumerate(((e,eo,det[:,None,None]*np.linalg.inv(g)),(b,bo,g/det[:,None,None]))):
            local=np.einsum('qai,qab,qbj,q->ij',basis,metric,basis,wt);minima[k]=min(minima[k],np.linalg.eigvalsh(local)[0]);ids=[grid[1][k+1][ax,tuple(np.array(p)+off)] for ax,off in offs]
            entries[k].append((np.repeat(ids,len(ids)),np.tile(ids,len(ids)),local.ravel()))
    out=[]
    for k,ls in enumerate(entries):
        r,c,v=(np.concatenate(a) for a in zip(*ls));out.append(coo_matrix((v,(r,c)),shape=(len(grid[0][k+1]),)*2).tocsr())
    assert min(minima)>0
    return out,minima

def norm(a):return np.linalg.norm(a.data)

def assay():
    c=ab.complex_grid(4);f=ab.complex_grid(12);R,H=ab.refine(4,c,f);I=[a.astype(float)/27 for a in H]
    (M,N),mins=assemble(f,12,3);(M2,N2),_=assemble(f,12,2);(Mc,Nc),_=assemble(c,4,5)
    errors=[norm(I[k].T@A@I[k]-B) for k,A,B in ((1,M,Mc),(2,N,Nc))]
    old=aa.assemble(order=3);assert np.max(abs(old[0]-assemble(c,4,3)[0][0].toarray()))<1e-12
    C=f[2][1];a=np.zeros(M.shape[0]);a[f[1][1][((1,),(10,1,1))]]=1;b=C@a;e=np.zeros_like(a);dt=.1
    em=spsolve((2*M+dt**2/2*C.T@N@C).tocsc(),dt*C.T@N@b);e1=2*em;b1=b-dt*C@em
    energy=abs((e1@M@e1+b1@N@b1-b@N@b)/2);gauss=np.max(abs(f[2][0].T@(M@e1)))
    assert energy<1e-10 and gauss<1e-10 and np.linalg.norm(R[1]@e1)>1e-8
    print('curved refined local SPD minima',mins,'quadrature 2->3',norm(M-M2),norm(N-N2),'Galerkin difference',errors,'coarse response',np.linalg.norm(R[1]@e1),'energy',energy,'Gauss',gauss)
if __name__=='__main__':assay()
