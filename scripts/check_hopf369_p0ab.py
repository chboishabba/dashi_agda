"""P0AB: signed cube frames, ternary cubical cochain refinement and seam defects.
Exact integer sparse identities; flat Galerkin Hodge regression, not radiation.
"""
from itertools import product, combinations, permutations
import numpy as np
from scipy.sparse import csr_matrix, kron, diags
from scipy.sparse.linalg import spsolve
import hopf369_exterior as aa

def sparse(entries,shape):
    r,c,v=zip(*entries) if entries else ([],[],[])
    return csr_matrix((np.array(v,dtype=np.int64),(r,c)),shape=shape)
def zero(A):
    A=A.tocsr();A.eliminate_zeros();return A.nnz==0

def complex_grid(n):
    cells=[];index=[]
    for k in range(4):
        c=[(axes,p) for axes in combinations(range(3),k) for p in product(*[range(n if i in axes else n+1) for i in range(3)])]
        cells.append(c);index.append({x:i for i,x in enumerate(c)})
    D=[]
    for k in range(3):
        entries=[]
        for i,(axes,p) in enumerate(cells[k+1]):
            for j,a in enumerate(axes):
                rest=axes[:j]+axes[j+1:];q=list(p);q[a]+=1;sign=(-1)**j
                entries.extend([(i,index[k][rest,p],-sign),(i,index[k][rest,tuple(q)],sign)])
        D.append(sparse(entries,(len(cells[k+1]),len(cells[k]))))
    assert all(zero(D[k+1]@D[k]) for k in range(2))
    return cells,index,D

def frame(n,grid,perm,sgn):
    cells,index,_=grid;U=[]
    for k in range(4):
        entries=[]
        for j,(axes,p) in enumerate(cells[k]):
            mapped=[perm[a] for a in axes];order=tuple(sorted(mapped));q=[0]*3
            sign=(-1)**sum(mapped[a]>mapped[b] for a in range(k) for b in range(a+1,k))
            for a in range(3):
                q[perm[a]]=p[a] if sgn[a]==1 else n-p[a]-int(a in axes)
                if a in axes:sign*=sgn[a]
            entries.append((index[k][order,tuple(q)],j,sign))
        U.append(sparse(entries,(len(cells[k]),len(cells[k]))))
    return U

def refine(n,coarse,fine):
    # I_k = H_k/27, common integer denominator for all degrees.
    # Nodal factor linear interpolation /3; edge factor integral /3.
    R=[];H=[]
    for k in range(4):
        rr=[];hh=[]
        for i,(axes,p) in enumerate(coarse[0][k]):
            for offsets in product(*[range(3) if a in axes else (0,) for a in range(3)]):
                q=tuple(3*p[a]+offsets[a] for a in range(3));rr.append((i,fine[1][k][axes,q],1))
        for i,(axes,p) in enumerate(fine[0][k]):
            opts=[]
            for a,x in enumerate(p):
                q,r=divmod(x,3)
                opts.append([(q,1)] if a in axes else [(q,3)] if r==0 else [(q,3-r),(q+1,r)])
            for v in product(*opts):
                q=tuple(x[0] for x in v);w=int(np.prod([x[1] for x in v]));hh.append((i,coarse[1][k][axes,q],w))
        R.append(sparse(rr,(len(coarse[0][k]),len(fine[0][k]))));H.append(sparse(hh,(len(fine[0][k]),len(coarse[0][k]))))
    for k in range(4):
        assert zero(R[k]@H[k]-27*diags(np.ones(R[k].shape[0],dtype=np.int64),dtype=np.int64))
    for k in range(3):
        assert zero(fine[2][k]@H[k]-H[k+1]@coarse[2][k])
        assert zero(R[k+1]@fine[2][k]-coarse[2][k]@R[k])
    return R,H

def flat_mass(n,k,length):
    # Unit-form basis, tensor products; exact Galerkin relation on common geometry.
    h=length/n
    M0=diags([np.ones(n)/6,np.r_[1,np.full(n-1,2),1]/3,np.ones(n)/6],[-1,0,1],format='csr')*h
    M1=diags(np.ones(n)/h,format='csr')
    from scipy.sparse import block_diag
    return block_diag([kron(kron(*[M1 if i in axes else M0 for i in (0,1)]),M1 if 2 in axes else M0) for axes in combinations(range(3),k)],format='csr')

def assay():
    coarse=complex_grid(4);fine=complex_grid(12);R,H=refine(4,coarse,fine)
    # Exact reuse of P0AA oriented incidence, not a same-size surrogate.
    assert np.array_equal(coarse[2][0].toarray(),aa.G.T)
    assert np.array_equal(coarse[2][1].toarray(),aa.C)
    assert np.array_equal(coarse[2][2].toarray(),aa.Z)
    count=0;proper=0
    for perm in permutations(range(3)):
        parity=(-1)**sum(perm[i]>perm[j] for i in range(3) for j in range(i+1,3))
        for sgn in product((-1,1),repeat=3):
            proper+=int(parity*np.prod(sgn)==1);Uc=frame(4,coarse,perm,sgn);Uf=frame(12,fine,perm,sgn)
            for k in range(4):
                for U in (Uc[k],Uf[k]):assert zero(U.T@U-diags(np.ones(U.shape[0],dtype=np.int64),dtype=np.int64))
                assert zero(R[k]@Uf[k]-Uc[k]@R[k]) and zero(H[k]@Uc[k]-Uf[k]@H[k])
            for k in range(3):
                for gr,U in ((coarse,Uc),(fine,Uf)):assert zero(gr[2][k]@U[k]-U[k+1]@gr[2][k])
            count+=1
    # Six Rubik layer quarter-turns, on original 27 vertices; cross-seam adjacency fails.
    small=complex_grid(2);turns=[]
    for axis in range(3):
        u,v=[i for i in range(3) if i!=axis]
        for side in (0,2):
            def turn(p):
                q=list(p)
                if p[axis]==side:q[u],q[v]=2-p[v],p[u]
                return tuple(q)
            defects=[]
            for axes,p in small[0][1]:
                q=list(p);q[axes[0]]+=1;q=tuple(q)
                a,b=turn(p),turn(q)
                if sum(abs(a[i]-b[i]) for i in range(3))!=1:defects.append((p,q,a,b))
            assert len(defects)==8
            assert all(turn(turn(turn(turn(p))))==p for _,p in small[0][0]);turns.append(defects)
    # Whole coarse/fine field, exact integer residual using common denominator.
    for k in range(4):
        x=np.arange(R[k].shape[1],dtype=np.int64)%19-9;obs=R[k]@x;res=27*x-H[k]@obs
        assert np.array_equal(R[k]@res,np.zeros(len(obs),dtype=np.int64))
        assert np.array_equal(H[k]@obs+res,27*x)
    # Galerkin Hodge and curl-energy compatibility (flat unit-coefficient control).
    err=[]
    for k in range(4):
        I=H[k].astype(float)/27;Mf=flat_mass(12,k,4);Mc=flat_mass(4,k,4)
        d=(I.T@Mf@I-Mc).tocoo();err.append(float(np.max(abs(d.data),initial=0)));assert err[-1]<1e-12
    # Actual original curved P0AA metric: frame transport is congruence, not a physical symmetry assertion.
    M,N,*_=aa.assemble(order=3);U=frame(4,coarse,(0,2,1),(1,1,-1));D=coarse[2][1];e=np.sin(np.arange(M.shape[0]));b=D@e
    Mt=U[1]@M@U[1].T;Nt=U[2]@N@U[2].T;et=U[1]@e;bt=U[2]@b
    energy0=(e@M@e+b@N@b)/2;energy1=(et@Mt@et+bt@Nt@bt)/2
    assert abs(energy1-energy0)<1e-10 and np.max(abs(D@et-bt))<1e-12
    # Fine exterior-only curl pulse, zero coarse field and zero original receiver trace.
    # Use a fine edge off every coarse edge, in the collar x>1.
    a=np.zeros(len(fine[0][1]));a[fine[1][1][((1,),(10,1,1))]]=1
    assert not np.any(R[1]@a)
    Cf=fine[2][1];bf=Cf@a;ef=np.zeros_like(a)
    assert not np.any(R[2]@bf) and not np.any(fine[2][2]@bf)
    assert all(bf[j]==0 for j,(axes,p) in enumerate(fine[0][2]) if all(3<=p[i]<=9-int(i in axes) for i in range(3)))
    Mf=flat_mass(12,1,4);Nf=flat_mass(12,2,4);dt=.1
    energy_before=(ef@(Mf@ef)+bf@(Nf@bf))/2
    em=spsolve((2*Mf+dt*dt/2*Cf.T@Nf@Cf).tocsc(),2*Mf@ef+dt*Cf.T@Nf@bf)
    ef1=2*em-ef;bf1=bf-dt*Cf@em
    energy_after=(ef1@(Mf@ef1)+bf1@(Nf@bf1))/2
    coarse_response=np.linalg.norm(R[1]@ef1);assert coarse_response>1e-8
    assert abs(energy_after-energy_before)<1e-10 and np.max(abs(fine[2][0].T@(Mf@ef1)))<1e-10
    print('invisible fine pulse coarse electric response',coarse_response,'energy closure',abs(energy_after-energy_before))
    print('frames',count,'proper',proper,'improper',count-proper,'seam defects per face',[len(x) for x in turns])
    print('coarse', [len(c) for c in coarse[0]],'fine',[len(c) for c in fine[0]],'residual dimensions',[R[k].shape[1]-R[k].shape[0] for k in range(4)])
    print('flat Galerkin Hodge max errors',err,'curved frame energy error',abs(energy1-energy0),'fixed-metric frame difference',np.linalg.norm(Mt-M))
if __name__=='__main__':assay()
