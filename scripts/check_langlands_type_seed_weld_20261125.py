from pathlib import Path
from runpy import run_path
from itertools import product, permutations
from collections import Counter
from random import Random
from sympy import Matrix, eye
import numpy as np

# Reuse original producers, including their previous executable controls.
root=Path(__file__).resolve().parent
wild=run_path(str(root/'check_langlands_wild_epsilon_20261125.py'))
aff=run_path(str(root/'check_langlands_affine_seed_20261125.py'))
cut=run_path(str(root/'check_langlands_green_cut_20261125.py'))
rng=Random(306); stats=Counter()
# Lattice-adapted basis: all K-coordinate 1's followed by all pi's.
P=Matrix([[0,-3],[1,3]])
assert 3*(eye(2)+2*P)*P**-5==Matrix([[6,21],[-7,-15]])/9
beta=np.kron(np.array([[6,21],[-7,-15]],dtype=np.int64),np.eye(4,dtype=np.int64))
I=np.eye(8,dtype=np.int64); I4=np.eye(4,dtype=np.int64)
# exp(2pi i Tr(beta X)/3) = zeta3^phase(X), for X in P_A^2=3A.
def phase(X):
    t=int(np.trace(beta@X));assert t%9==0;return t//9%3

def ideal(X):
    return not np.any(X%3) and not np.any(X[:4,4:]%9)

def random_matrix():return np.array([[rng.randrange(-9,10) for _ in range(4)] for _ in range(4)],dtype=np.int64)
def rad2():return np.block([[3*random_matrix(),9*random_matrix()],[3*random_matrix(),3*random_matrix()]])
def embed(C,D):return np.block([[C,-3*D],[D,C+3*D]])
rm=wild['rm']; red=wild['red']; addK=wild['add']; chi=wild['chi']
perms=[(p,(-1)**sum(p[i]>p[j] for i in range(4) for j in range(i+1,4))) for p in permutations(range(4))]
def determinant(C,D):
    t=(0,0)
    for p,s in perms:
        v=(s,0)
        for i,j in enumerate(p):v=rm(v,(int(C[i,j]),int(D[i,j])))
        t=red(addK(t,v))
    return t
# Every basis direction of the overlap (and all scalar residue lifts).
for a,b in product(range(9),repeat=2):
    C=I4.copy();D=np.zeros((4,4),dtype=np.int64);C[0,0]+=3*a;D[0,0]=3*b
    assert phase(embed(C,D)-I)==chi[determinant(C,D)];stats['scalar_overlap']+=1
for i,j in product(range(4),repeat=2):
    for a,b in product(range(3),repeat=2):
        C=I4.copy();D=np.zeros((4,4),dtype=np.int64);C[i,j]+=3*a;D[i,j]=3*b
        assert phase(embed(C,D)-I)==chi[determinant(C,D)];stats['basis_overlap']+=1
# Verify on exact 8x8 matrix representatives, including pi conjugation.
Pi=np.kron(np.array([[0,-3],[1,3]],dtype=np.int64),I4)
PiInv3=np.kron(np.array([[3,3],[-1,0]],dtype=np.int64),I4)
assert np.array_equal(Pi@PiInv3,3*I)
for _ in range(120):
    X,Y=rad2(),rad2();assert ideal(X) and ideal(Y)
    assert phase(X@Y)==0 and phase(X+Y+X@Y)==(phase(X)+phase(Y))%3
    stats['radical_products']+=1
    Z=Pi@X@PiInv3;assert not np.any(Z%3);Z=Z//3
    assert ideal(Z) and phase(Z)==phase(X);stats['uniformizer_gauge']+=1
    C=I4+3*random_matrix();D=3*random_matrix();k=embed(C,D)
    assert phase(k-I)==chi[determinant(C,D)];stats['matrix_overlap']+=1
    # elementary K-linear unit (inverse exact) centralizes beta and normalizes 3A.
    i,j=rng.sample(range(4),2);C=I4.copy();D=np.zeros((4,4),dtype=np.int64)
    C[i,j]=rng.randrange(9);D[i,j]=rng.randrange(9);k=embed(C,D);ki=2*I-k
    assert np.array_equal(k@ki,I) and ideal(k@X@ki) and phase(k@X@ki)==phase(X)
    stats['centralizer_gauge']+=1
# Explicit factorization ambiguity k u = (k h)(h^-1 u) for h in overlap.
for _ in range(80):
    i,j=rng.sample(range(4),2);C=I4.copy();D=np.zeros((4,4),dtype=np.int64)
    C[i,j]=3*rng.randrange(9);D[i,j]=3*rng.randrange(9);h=embed(C,D);hi=2*I-h
    X=rad2();assert phase(hi@(I+X)-I)==(phase(X)-chi[determinant(C,D)])%3
    stats['factorization_gauge']+=1

# Compose R283 affine elimination with R295 target-conditioned cut, plus
# R201/R58 canonical residual prefix alternative. Same source / label chart.
rref,mv,project,seedsolve,norm,step,sat,packet=[aff[k] for k in ('rref','mv','project','seedsolve','norm','step','sat','packet')]
add,sub,basis,contains,solve=[cut[k] for k in ('add','sub','basis','contains','solve')]
def residual(n,A,B,target,F,w,v,order,diagonal,mod=None):
    ds=[(0,0),(1,1)] if diagonal else list(product(range(2),repeat=2));zero=(0,)*len(target)
    def cv(i,d):return tuple((d[0]*a+d[1]*b)%3 for a,b in zip(A[i],B[i]))
    T={(tuple(norm(C) for C in F),zero,0,0,0):(1,{})}; peak=1;trans=0
    for j,i in enumerate(order):
        Q=basis(cv(k,d) for k in order[j+1:] for d in ds);P=basis(cv(k,d) for k in order[:j+1] for d in ds)
        lam=len(P)+len(Q)-len(basis([*P.values(),*Q.values()]));U={}
        for (R,s,t,k,l),(count,path) in T.items():
            for d in ds:
                trans+=1;NR=tuple(step(R[a],i,d[a//2]) for a in range(4))
                if (NR[0] is None or NR[2] is None) and (NR[1] is None or NR[3] is None):continue
                z=add(s,cv(i,d))
                if not contains(Q,sub(target,z)):continue
                key=(NR,z,(t+w[i]*d[0]-v[i]*d[1])%3,k+d[0]*(i==0),l+d[1]*(i==0));c,p=U.get(key,(0,path|{i:d}));U[key]=((c+count) if mod is None else (c+count)%mod,p)
        assert len(U)<=len({k[0] for k in U})*3**lam*12
        T=U;peak=max(peak,len(T));stats['residual_bounds']+=1
    out=Counter();back={}
    for (R,s,t,k,l),(count,p) in T.items():
        assert s==target and all(r in (None,()) for r in R)
        st=int(R[0]==() and R[2]==())+2*int(R[1]==() and R[3]==())
        if st:
            key=(t,k+1,l+1,st);out[key]+=count
            if mod is not None:out[key]%=mod
            back[key]=p
    return out,back,peak,trans

def compile_affine(A,C,B,D,u,v,pins,n,d):
    M=A+C+[[int(i==j) for j in range(d)] for i in pins];R,E,piv=rref(M,d);Q=E[len(piv):]
    U=project(Q,B+[[0]*n for _ in range(len(C)+len(pins))],n)
    V=project(Q,[[0]*n for _ in A]+D+[[0]*n for _ in pins],n)
    target=tuple(-x%3 for x in mv(Q,u+v+tuple(pins.values())))
    return M,R,E,piv,U,V,target

for n in range(1,6):
    for trial in range(10):
        d=1+trial%4;a=1+trial%3;b=1+(trial//2)%3
        def mat(r,c):return [[rng.randrange(3) for _ in range(c)] for _ in range(r)]
        A,C,B,D=mat(a,d),mat(b,d),mat(a,n),mat(b,n)
        u=tuple(rng.randrange(3) for _ in A);v=tuple(rng.randrange(3) for _ in C)
        pins={i:rng.randrange(3) for i in range(d) if rng.randrange(4)==0}
        M,R,E,piv,U,V,target=compile_affine(A,C,B,D,u,v,pins,n,d);e=d-len(piv);mult=3**e
        def cnf():return [tuple((i+1)*rng.choice((-1,1)) for i in rng.sample(range(n),rng.randrange(1,min(n,3)+1))) for _ in range(rng.randrange(5))]
        F=[cnf() for _ in range(4)];clauses=[(tuple(abs(z)-1 for z in c),tuple(int(z>0) for z in c),i) for i,f in enumerate(F) for c in f]
        w=[rng.randrange(3) for _ in range(n)];z=[rng.randrange(3) for _ in range(n)];order=list(range(n));rng.shuffle(order)
        def rhs(x,y):return add(mv(B,x),u)+add(mv(D,y),v)+tuple(pins.values())
        def label(x,y):
            st=int(sat(F[0],x) and sat(F[2],y))+2*int(sat(F[1],x) and sat(F[3],y))
            return (sum(a*b-c*d for a,b,c,d in zip(w,x,z,y))%3,x[0]+1,y[0]+1,st)
        for diag in (False,True):
            ref=Counter()
            for x,y in product(product(range(2),repeat=n),repeat=2):
                if diag and x!=y:continue
                key=label(x,y)
                if not key[-1]:continue
                r=rhs(x,y);cnt=sum(mv(M,s)==r for s in product(range(3),repeat=d))
                if cnt:ref[key]+=cnt
            for mod in (None,1,3,9,27,16):
                need=None if mod is None else (mod//(3**min(e,{1:0,3:1,9:2,27:3}[mod])) if mod in (1,3,9,27) else mod)
                c,bc,st=solve(n,U,V,target,clauses,w,z,order,diag,need)
                r,br,peak,trans=residual(n,U,V,target,F,w,z,order,diag,need)
                expected={k:(v if mod is None else v%mod) for k,v in ref.items()}
                for tab,back in ((c,bc),(r,br)):
                    assert set(tab)==set(ref)==set(back)
                    assert {k:(v*mult if mod is None else v*mult%mod) for k,v in tab.items()}==expected
                    for k,path in back.items():
                        x,y=zip(*(path[i] for i in range(n)));assert label(x,y)==k and (not diag or x==y)
                        free=[i for i in range(d) if i not in piv];f=tuple(rng.randrange(3) for _ in free);s=seedsolve(R,E,piv,rhs(x,y),d,f)
                        assert s is not None and mv(M,s)==rhs(x,y) and tuple(s[i] for i in free)==f
                        stats['original_reopens']+=1
                if mod is None:
                    assert packet(Counter({k:v*mult for k,v in c.items()}))==packet(ref)
                    stats['exact_packet']+=1
                else:stats['modular_support']+=1
                if need==1:stats['occupancy_only']+=1
            stats['fixture_modes']+=1
# Dense source with many crossing clauses but only two residual formulas.
for m in (8,16,32):
    n=2*m;F=[[(i+1,m+j+1) for i in range(m) for j in range(m)]]*4
    out,back,peak,trans=residual(n,[()]*n,[()]*n,(),F,[0]*n,[0]*n,list(range(n)),True)
    assert sum(out.values())==2**(m+1)-1 and peak<=3
    print('dense original diagonal',m,sum(out.values()),peak,trans,flush=True)
print('TYPE AND SEED WELD PASS',dict(stats),flush=True)
