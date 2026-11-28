"""Endpoint welds on original donors; finite checks, not continuum/kernel claims."""
import argparse
import inspect
import numpy as np
import sympy as s
from itertools import combinations,product


def atomic():
    # Full exterior-square inverse, with arbitrary signed matrix entries.
    d=8; pairs=list(combinations(range(d),2)); A=s.Matrix(d,d,lambda i,j:s.Symbol('a%d%d'%(i,j)))
    delta=lambda i,j:int(i==j)
    L=s.Matrix(28,28,lambda u,v:A[pairs[u][0],pairs[v][0]]*delta(pairs[u][1],pairs[v][1])+delta(pairs[u][0],pairs[v][0])*A[pairs[u][1],pairs[v][1]]-A[pairs[u][0],pairs[v][1]]*delta(pairs[u][1],pairs[v][0])-delta(pairs[u][0],pairs[v][1])*A[pairs[u][1],pairs[v][0]])
    def entry(i,k,j,l):
        if i==k or j==l:return 0
        return (1 if i<k else -1)*(1 if j<l else -1)*L[pairs.index(tuple(sorted((i,k)))),pairs.index(tuple(sorted((j,l))))]
    T=s.Matrix(d,d,lambda i,j:sum(entry(i,k,j,k) for k in range(d)))
    assert (T-(d-2)*A-s.trace(A)*s.eye(d)).applyfunc(s.expand)==s.zeros(d)
    assert ((T-s.trace(T)*s.eye(d)/(2*(d-1)))/(d-2)-A).applyfunc(s.expand)==s.zeros(d)
    print('BR268 exact 64-entry exterior-square inverse; subtract authenticated Coulomb first; unknown radial scale not inferred')


def g4():
    from check_hopf369_br230_233_dynamic_cut import conserved,primitive
    rng=np.random.default_rng(369);err=0.; margin=1.
    for _ in range(24):
        M=np.eye(3)+rng.normal(size=(3,3))*.15;h=M.T@M
        q=2.;v=rng.normal(size=3)*.12;B=rng.normal(size=3)*.3; C=.5
        # Orthonormal frame inverse is the existing BR227/232 inverse.
        U=conserved(q,v,B,C);r,w,b,p=primitive(U,B[0],C)
        vc=np.linalg.solve(M,w);bc=np.linalg.solve(M,b);jc=M.T@U[1:4]
        E=-np.cross(w,b);S=q*np.outer(w,w)+p*np.eye(3)+(b@b+E@E)/2*np.eye(3)-np.outer(b,b)-np.outer(E,E)
        Sc=M.T@S@M;root=np.sqrt(np.linalg.det(h));beta=rng.normal(size=3)*.05;alpha=1.1
        g=np.block([[np.array([[-alpha**2+beta@h@beta]]),(h@beta)[None,:]],[(h@beta)[:,None],h]])
        normal=np.r_[1.,-beta]/alpha;J=np.r_[beta@jc,jc];nc=g@normal
        T=U[0]*np.outer(nc,nc)+np.outer(nc,J)+np.outer(J,nc)+np.block([[np.array([[beta@Sc@beta]]),(Sc@beta)[None,:]],[(Sc@beta)[:,None],Sc]])
        err=max(err,abs(normal@T@normal-U[0]),np.max(abs(-(normal@T)[1:]-jc)),abs(vc@h@vc-w@w),abs(bc@h@bc-b@b),abs(root-np.linalg.det(M)))
        margin=min(margin,1-v@v,p,p+C)
    assert err<1e-10 and margin>0
    print('BR269 curved-frame stress/primitive weld',err,'margin',margin,'24 fixtures; no York or coupled evolution')


def material():
    import check_hopf369_br241_metric_consumer as d
    from scipy.interpolate import RegularGridInterpolator
    from numpy.polynomial.legendre import leggauss
    z=d.donor.z
    def assembly(g,order=3):
        grid=np.linspace(-1.5,1.5,g.shape[0]);sample=RegularGridInterpolator((grid,)*3,g[...,:4,:4],bounds_error=True)
        M=np.zeros((54,54));Ma=M.copy();N=np.zeros((36,36));L=np.zeros((54,36));t,w=leggauss(order);t=(t+1)/2;w=w/2; margin=1e9;shift=0.
        for p in z.cells:
            for ijk in product(range(order),repeat=3):
                x=t[list(ijk)];e,b=z.basis(p,x);G=sample(np.array(p)+x-1)[0];h=G[1:,1:];beta=np.linalg.solve(h,G[0,1:]);alpha=np.sqrt(beta@h@beta-G[0,0]);root=np.sqrt(np.linalg.det(h));W=root*np.linalg.inv(h);wt=np.prod(w[list(ijk)])
                margin=min(margin,alpha-np.sqrt(beta@h@beta));shift=max(shift,np.linalg.norm(beta))
                M+=wt*e.T@W@e;Ma+=wt*alpha*e.T@W@e;N+=wt*alpha*b.T@(h/root)@b;L+=wt*(W@e).T@np.cross(beta,b.T).T
        K=np.linalg.inv(M);H=np.block([[K@Ma@K,K@L],[L.T@K,N]]);H=(H+H.T)/2
        _,V=d.assembly(g,order);assert margin>0 and np.linalg.eigvalsh(H)[0]>0
        print('BR270 spacetime assembly margin',margin,'shift',shift,'cross',np.linalg.norm(K@L),flush=True)
        return H,V
    ns=dict(vars(d),assembly=assembly);exec(inspect.getsource(d.material),ns);ns['material'](11)


def history():
    from check_hopf369_br240_metric_history import run
    gs,dx=run(11,full=True);g0=gs[0][5,5,5];g1=gs[-1][5,5,5]
    # Exact inverse of the KK Schur chart; reflection of the marked fibre.
    def split(g):
        r=g[4,4];a=g[:4,4]/r;return g[:4,:4]-r*np.outer(a,a),a,r
    def join(q):
        h,a,r=q;return np.block([[h+r*np.outer(a,a),r*a[:,None]],[r*a[None,:],np.array([[r]])]])
    R=np.diag([1,1,1,1,-1]);err=0.
    for g in (g0,g1):
        h,a,r=split(g);err=max(err,np.max(abs(join((h,a,r))-g)),np.max(abs(join((h,-a,r))-R@g@R)))
    delta=g1-g0; # history translation as a marked arrow, not an autonomous physical evolution
    residual=(R@(g0+delta)@R)-(R@g0@R+delta)
    assert err<1e-12 and np.linalg.norm(residual)>0
    print('BR271 actual history KK reopen/reflection',err,'fixed-arrow chronology/reflection residual',np.linalg.norm(residual))


def analytic():
    # Coefficient recursion of a general linear noncharacteristic second-order
    # system, with arbitrary spatial jets represented by a polynomial basis.
    t=s.symbols('t'); A=s.Matrix([[2,1],[1,3]]);B=s.Matrix([[1,2],[3,1]]);K=s.Matrix([[3,1],[0,2]])
    u=[s.zeros(2,1),s.zeros(2,1)]
    for m in range(8):
        poly=sum((t**i*u[i] for i in range(len(u))),s.zeros(2,1));rhs=(B*poly.diff(t)+(K+t*B)*poly).applyfunc(lambda z:s.expand(z).coeff(t,m));u.append(A.inv()*rhs/((m+1)*(m+2)))
    assert all(v==s.zeros(2,1) for v in u)
    print('BR272 finite zero-jet recursion fixture; analytic uniqueness requires actual noncharacteristic analytic solution')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['atomic','g4','material','history','analytic'],required=True);globals()[p.parse_args().part]()
