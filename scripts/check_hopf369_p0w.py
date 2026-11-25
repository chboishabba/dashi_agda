"""P0W: cubical de Rham receiver on original non-null KK section.
Numerical Hodge quadrature, not a coupled exterior or spacetime solve.
"""
import numpy as np
import sympy as s
from itertools import product, combinations
from scipy.integrate import solve_ivp, quad
from numpy.polynomial.legendre import leggauss
P=list(product((-1,0,1),repeat=3)); E=[]; F=[]; V=list(product((-1,0),repeat=3))
for i in range(3):
    for a in (-1,0):
        for q in product((-1,0,1),repeat=2):
            p=list(q);p.insert(i,a);E.append((i,tuple(p)))
for i,j in combinations(range(3),2):
    k=3-i-j
    for a,b,c in product((-1,0),(-1,0),(-1,0,1)):
        p=[c]*3;p[i]=a;p[j]=b;F.append((i,j,tuple(p)))
G=np.zeros((27,54),int); C=np.zeros((36,54),int); Z=np.zeros((8,36),int)
def shift(p,i):
    q=list(p);q[i]+=1;return tuple(q)
for l,(i,p) in enumerate(E):G[P.index(p),l]=-1;G[P.index(shift(p,i)),l]=1
for l,(i,j,p) in enumerate(F):
    for k,q,sgn in ((i,p,1),(j,shift(p,i),1),(i,shift(p,j),-1),(j,p,-1)):C[l,E.index((k,q))]=sgn
for l,p in enumerate(V):
    for k in range(3):
        i,j=[a for a in range(3) if a!=k];sgn=(-1)**k
        Z[l,F.index((i,j,p))]=-sgn;Z[l,F.index((i,j,shift(p,k)))]=sgn
assert not np.any(C@G.T) and not np.any(Z@C)
assert [s.Matrix(a).rank() for a in (G,C,Z)]==[26,28,8]
assert sum(np.count_nonzero(Z,axis=0)==1)==24
# Local tensor-product basis of cubical differential forms, signed 2-form represented as flux vector.
def basis(p,x):
    e=np.zeros((3,54));b=np.zeros((3,36))
    for l,(i,q) in enumerate(E):
        d=np.array(q)-p
        if d[i]==0 and all(d[j] in (0,1) for j in range(3)):
            e[i,l]=np.prod([x[j] if d[j] else 1-x[j] for j in range(3) if j!=i])
    for l,(i,j,q) in enumerate(F):
        k=3-i-j;d=np.array(q)-p
        if d[i]==d[j]==0 and d[k] in (0,1):b[k,l]=(-1)**k*(x[k] if d[k] else 1-x[k])
    return e,b
# Verify polynomial curl and divergence against original incidence on all cells.
for p in V:
    es,bs=basis(p,np.array([.25,.5,.75])); deriv=[]; db=[]
    for k in range(3):
        x=np.zeros(3);x[k]=1;y=np.zeros(3);y[k]=0
        for j in range(3):
            if j!=k:x[j]=y[j]=[.25,.5,.75][j]
        e1,b1=basis(p,x);e0,b0=basis(p,y);deriv.append(e1-e0);db.append(b1-b0)
    curl=np.array([deriv[1][2]-deriv[2][1],deriv[2][0]-deriv[0][2],deriv[0][1]-deriv[1][0]])
    assert np.array_equal(curl,bs@C)
    assert np.array_equal(sum(db[k][k] for k in range(3)),Z[V.index(p)])
# Original P0T radial KK conformal factor. Normalize u=r psi at large R by u'(R).
eps=.25; R=64.
def potential(r):return eps**2*64/(12*(1+r*r)**4)
sol=solve_ivp(lambda r,u:[u[1],-potential(r)*u[0]],(0,R),[0,1],rtol=2e-12,atol=2e-14,dense_output=True)
normal=sol.y[1,-1]
def psi(r):return (sol.sol(r)[0]/r if r else 1.)/normal
def A(x):
    x,y,z=x;d=1+x*x+y*y+z*z;return 2*np.array([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/d**2
def metric(x,section):
    a=eps*A(x);return psi(np.linalg.norm(x))**2*(np.eye(3)+(np.outer(a,a) if section else 0))
def weights(g):
    d=np.sqrt(np.linalg.det(g));return d*np.linalg.inv(g),g/d
# All native oriented edge integrals from the original potential.
a=np.array([eps*quad(lambda t:A(np.array(p)+np.eye(3)[i]*t)[i],0,1,epsabs=1e-13)[0] for i,p in E]); b=C@a
assert np.max(abs(Z@b))<1e-13

def assemble(order,section):
    t,w=leggauss(order);t=(t+1)/2;w=w/2;M=np.zeros((54,54));N=np.zeros((36,36));port=np.zeros((54,36))
    for p in V:
        for ijk in product(range(order),repeat=3):
            x=t[list(ijk)];e,f=basis(p,x);m,n=weights(metric(np.array(p)+x,section));wt=np.prod(w[list(ijk)])
            M+=wt*e.T@m@e;N+=wt*f.T@n@f
        for k in range(3):
            for side in (0,1):
                if p[k]+side not in (-1,1):continue
                ij=[i for i in range(3) if i!=k];normal=np.eye(3)[k]*(2*side-1)
                for u,v in product(range(order),repeat=2):
                    x=np.zeros(3);x[k]=side;x[ij]=[t[u],t[v]];e,f=basis(p,x);_,n=weights(metric(np.array(p)+x,section))
                    port+=w[u]*w[v]*np.cross(normal,e.T)@n@f
    return M,N,port
M,N,T=assemble(6,True); M8,N8,T8=assemble(8,True); Mb,Nb,Tb=assemble(6,False)
assert min(np.linalg.eigvalsh(M8))>0 and min(np.linalg.eigvalsh(N8))>0
assert np.linalg.norm(M-Mb)>0 and np.linalg.norm(N-Nb)>0
# Selected prescribed boundary trace and current comparator, no physical exterior solution.
e0=a; b0=b;dt=.04;p=T8@b0;j=.1*M8@e0
em=np.linalg.solve(2*M8+dt**2/2*C.T@N8@C,2*M8@e0+dt*(C.T@N8@b0-j-p))
e1=2*em-e0;b1=b0-dt*C@em
energy=lambda e,b:.5*(e@M8@e+b@N8@b)
closure=energy(e1,b1)-energy(e0,b0)+dt*em@(j+p)
assert abs(closure)<1e-12
assert np.max(abs(Z@(b1-b0)))<1e-12
# Weak Gauss: -Gd-Q+q_boundary. Both charge and boundary updates retained.
d0=M8@e0;d1=M8@e1;Q0=-G@d0;q0=np.zeros(27);jb=np.zeros(27)
Q1=Q0+dt*(G@j-jb);q1=q0-dt*(G@p+jb)
gauss=np.max(abs(-G@d1-Q1+q1));assert gauss<1e-12
# exact determinant/inverse rank-one and resolvent middle-factor derivative.
u,v,w,k=s.symbols('u v w k',real=True);x=s.Matrix([u,v,w]);I=s.eye(3);L=I+k*x*x.T
assert s.simplify(L.det()-1-k*x.dot(x))==0
assert (L*(I-k*x*x.T/(1+k*x.dot(x)))-I).applyfunc(s.simplify)==s.zeros(3)
print(dict(ranks=(26,28,8),boundary_faces=24,psi0=psi(0),eigmin=(float(np.linalg.eigvalsh(M8)[0]),float(np.linalg.eigvalsh(N8)[0])),metric_difference=(float(np.linalg.norm(M-Mb)),float(np.linalg.norm(N-Nb))),quadrature_difference=(float(np.linalg.norm(M-M8)),float(np.linalg.norm(N-N8)),float(np.linalg.norm(T-T8))),energy_closure=float(closure),gauss=float(gauss),port_work=float(dt*em@p),current_work=float(dt*em@j)))
