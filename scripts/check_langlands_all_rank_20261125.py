"""Exact finite controls for the all-rank Weil factor theorem (not an epsilon oracle)."""
from collections import Counter
from itertools import product
import random
import sympy as S

def run():
    R=S.Matrix([[-1,-1],[1,0]]); J=S.Matrix([[0,1],[1,0]])
    group=[R**i*J**j for i in range(3) for j in range(2)]
    I=S.eye(2); T=S.symbols('T'); rng=random.Random(209)
    # Compute inertia invariants and actual Frobenius restriction for finite S3 probes,
    # including an admissible nonzero-monodromy block with Phi N Phi^-1=N/3.
    def carrier(kind,length):
        rho=[S.eye(1) if kind==0 else S.Matrix([[g.det()]]) if kind==1 else g for g in group]
        d=rho[0].rows; F=S.kronecker_product(S.diag(*[S.Rational(1,3)**i for i in range(length)]),S.eye(d))
        N=S.kronecker_product(S.Matrix(length,length,lambda i,j: int(i==j+1)),S.eye(d))
        assert F*N*F.inv()==N/3
        return [S.kronecker_product(S.eye(length),g) for g in rho],F,N
    def eigdet(rho,F,N):
        d=F.rows; stacked=S.Matrix.vstack(N,*[g-S.eye(d) for g in rho]); K=stacked.nullspace()
        if not K:return S.Integer(1)
        C=S.Matrix.hstack(*K); A=C.gauss_jordan_solve(F*C)[0]
        return S.expand((S.eye(A.rows)-T*A).det())
    det_checks=0
    for kind,length,b,tag in product(range(3),(1,2,3),(0,1),(1,-1)):
        rho,F,N=carrier(kind,length)
        r0=eigdet(rho,F,N); ru=eigdet([S.kronecker_product(g,h) for g,h in zip(group,rho)],S.kronecker_product(I,F),S.kronecker_product(I,N))
        block=[S.diag(S.eye(1),g,g,g) for g in group]
        Phi=S.diag(1,1,1,(-1)**b,(-1)**b,(-1)**b,(-1)**b)
        direct=eigdet([S.kronecker_product(g,h) for g,h in zip(block,rho)],tag*S.kronecker_product(Phi,F),S.kronecker_product(S.eye(7),N))
        expected=r0.subs(T,tag*T)*ru.subs(T,tag*T)*ru.subs(T,tag*(-1)**b*T)**2
        assert S.expand(direct-expected)==0;det_checks+=1
    # Histogram classification in mu_(2m), with an arbitrary finite tag set.
    hist_checks=collisions=0
    for m in (2,3,4,5,7,8,15):
        for _ in range(80):
            A=[rng.randrange(6) for _ in range(2*m)];W=[rng.randrange(a+1) for a in A]
            E=[3*A[i]-2*W[i]+2*W[(i+m)%(2*m)] for i in range(2*m)]
            X=[W[i]-W[(i+m)%(2*m)] for i in range(2*m)]
            assert all((3*A[i]-E[i])//2==X[i] for i in range(2*m))
            V=W[:]
            for i in range(m):
                j=i+m; lo=-min(V[i],V[j]); hi=min(A[i]-V[i],A[j]-V[j]);d=rng.randint(lo,hi);V[i]+=d;V[j]+=d
            assert E==[3*A[i]-2*V[i]+2*V[(i+m)%(2*m)] for i in range(2*m)]
            collisions+=int(V!=W);hist_checks+=1
            # odd-order tag subgroup consists of even exponents, opposite coset odd
            if m%2:
                A=[a if i%2==0 else 0 for i,a in enumerate(A)];W=[w if i%2==0 else 0 for i,w in enumerate(W)]
                E=[3*A[i]-2*W[i]+2*W[(i+m)%(2*m)] for i in range(2*m)]
                assert all(E[(i+m)%(2*m)]==2*W[i] for i in range(0,2*m,2))
    # F_8 and F_16 exact field multiplication, explicit SAT formula for collision.
    def mul(a,b,d,poly):
        v=0
        while b:
            if b&1:v^=a
            b>>=1;a<<=1
            if a&(1<<d):a^=poly
        return v
    def weight(x,z,d,p):
        a=1
        for b,t in zip(x,z):
            if b:a=mul(a,t,d,p)
        return a
    def sat(F,x):return all(any(x[abs(l)-1]==int(l>0) for l in C) for C in F)
    blind=source_checks=0
    for d,poly in ((3,0b1011),(4,0b10011)):
        for _ in range(64):
            t=3;n=d*t;tags=[[rng.randrange(1,1<<d) for _ in range(n)] for _ in range(t)];F=[];pairs=[]
            for j in range(t):
                seen={};z=tags[j][j*d:(j+1)*d]
                for x in product((0,1),repeat=d):
                    a=weight(x,z,d,poly)
                    if a in seen: u=seen[a];v=x;break
                    seen[a]=x
                else:raise AssertionError('pigeonhole')
                pairs.append((u,v));pivot=next(i for i in range(d) if u[i]!=v[i]);k=j*d+pivot+1
                for i in range(d):
                    l=j*d+i+1
                    if u[i]==v[i]:F.append((l if u[i] else -l,))
                    elif i!=pivot:
                        F.extend(((-k,l),(k,-l)) if u[i]==u[pivot] else ((-k,-l),(k,l)))
                allowed={x for x in product((0,1),repeat=d) if sat([tuple((abs(l)-j*d)*(1 if l>0 else -1) for l in C) for C in F if all(j*d<abs(l)<=(j+1)*d for l in C)],x)}
                assert allowed=={u,v};source_checks+=1
            witnesses=[sum(x,()) for x in product(*pairs)];assert len(set(witnesses))==2**t and all(sat(F,x) for x in witnesses)
            for z in tags:
                a=0
                for x in witnesses:a^=weight(x,z,d,poly)
                assert a==0;blind+=1
    return dict(actual_WD_determinants=det_checks,histograms=hist_checks,nontrivial_even_tag_collisions=collisions,block_source_equivalence=source_checks,blind_samples=blind)
if __name__=='__main__':print(run())
