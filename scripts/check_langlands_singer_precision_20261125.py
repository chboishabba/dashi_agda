"""Actual Singer-tag local-factor precision, source witnesses and finite controls."""
from itertools import product
from collections import Counter
from math import comb
import random
import sympy as S
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ

def run():
    rng=random.Random(216); m=13
    M=S.Matrix([[1,1,0],[0,1,1],[1,1,1]]); r=S.ones(3,1); N=M.inv_mod(3).T
    D={i for i in range(m) if int((r.T*M**i*r)[0])%3==0}
    assert D=={0,6,10,11} and (M**13).applyfunc(lambda x:x%3)==S.eye(3)
    B=S.Matrix(m,m,lambda i,j:int((i-j)%m in D)); J=S.ones(m)
    assert all(B[i,j]==int(int(((M**i*r).T*(N**j*r))[0])%3==0) for i,j in product(range(m),repeat=2))
    assert B.T*B==B*B.T==3*S.eye(m)+J
    assert B* (B.T/3-J/12)==S.eye(m)
    snf=list(smith_normal_form(B,domain=ZZ).diagonal());assert snf==[1]*7+[3]*5+[12]
    assert {pow(2,j,13) for j in range(12)}==set(range(1,13))
    # Work in Z/(2^H)[z]/Phi_13, with cyclic 13-vector representatives.
    def canon(a,q):return tuple((a[i]-a[12])%q for i in range(12))+(0,)
    def plus(a,b,q):return tuple((x+y)%q for x,y in zip(a,b))
    def scale(a,c,q):return tuple(x*c%q for x in a)
    def shift(a,k,q):return canon([a[(i-k)%13] for i in range(13)],q)
    zero=(0,)*13;one=(1,)+(0,)*12
    def moment(W,k,q):
        a=[0]*13
        for j,w in enumerate(W):a[j*k%13]+=w
        return canon(a,q)
    def series(W,q,L):
        a=[one]+[zero]*L
        for j,w in enumerate(W):
            # (1+T)^(2w) * (1-T)^(-2w), at T=z^j T
            if not w:continue
            f=[sum(comb(2*w,i)*comb(2*w+k-i-1,k-i) for i in range(min(2*w,k)+1))%q for k in range(L+1)]
            b=[zero]*(L+1)
            for k in range(L+1):
                for i in range(k+1):
                    if f[i]:b[k]=plus(b[k],scale(shift(a[k-i],j*i,q),f[i],q),q)
            a=b
        return a
    def mul(a,b,q):
        out=zero
        for j,v in enumerate(b):
            if v:out=plus(out,scale(shift(a,j,q),v,q),q)
        return out
    checks=series_checks=derivative_checks=moment_checks=0
    for h in range(1,5):
        q=2**h;Q=4*q
        for _ in range(12):
            W=[rng.randrange(2*q) for _ in range(13)]
            V=[w+q*rng.randrange(3) for w in W];U=V[:];U[rng.randrange(13)]+=q//2
            a=series(W,Q,13);b=series(V,Q,13);c=series(U,Q,13)
            assert a==b and a!=c;series_checks+=2
            ell=[zero]*14
            for k in range(1,14):
                z=scale(a[k],k,Q)
                for i in range(1,k):z=plus(z,scale(mul(a[i],ell[k-i],Q),-1,Q),Q)
                ell[k]=z
                assert z==(scale(moment(W,k,Q),4,Q) if k%2 else zero);derivative_checks+=1
            # Two odd moments: k=1 gives relative coordinates, k=13 total.
            coeff=[v//4 for v in ell[1]][:12];total=ell[13][0]//4
            last=(total-sum(coeff))*pow(13,-1,q)%q
            assert [(c+last)%q for c in coeff]+[last]==[w%q for w in W];moment_checks+=1
            Y=list(B*S.Matrix(W));back=B.T*S.Matrix(Y)-sum(W)*S.ones(13,1)
            assert [int(v)*pow(3,-1,q)%q for v in back]==[w%q for w in W];checks+=1
            for k in range(1,13):
                assert moment(Y,k,q)==mul(moment(W,k,q),moment([int(j in D) for j in range(13)],k,q),q);checks+=1
        # Constant collision with full order 13: relative data retained, total needed.
        w=[0]*13;v=[q//2]*13
        assert moment(w,1,q)==moment(v,1,q) and moment(w,13,q)!=moment(v,13,q)
    # Actual source histograms and shifted rank-eight pole counts.
    pole_checks=0
    for _ in range(64):
        n=5;tags=[rng.randrange(13) for _ in range(n)];F=[tuple((1 if rng.randrange(2) else -1)*rng.randrange(1,n+1) for _ in range(3)) for _ in range(4)]
        W=[0]*13;Y=[0]*13
        for x in product((0,1),repeat=n):
            j=sum(a*b for a,b in zip(tags,x))%13
            if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F):
                W[j]+=1
                for d in D:Y[(j+d)%13]+=2
        assert Y==list(2*B*S.Matrix(W));pole_checks+=13
    # Joint query tag collision: exact prefix-complement CNF with K witnesses.
    def trie_cnf(words,n):
        F=[];P={()}
        for k in range(n):
            Q={w[:k+1] for w in words}
            for p in P:
                for b in (0,1):
                    t=p+(b,)
                    if t not in Q:F.append(tuple(-i-1 if x else i+1 for i,x in enumerate(t)))
            P=Q
        return F
    blind_checks=source_checks=balance_checks=0
    for n in range(4,10):
        for h in (1,2):
            K=2**h
            for _ in range(12):
                orders=(3,3) if 2**n>9*(K-1) else (3,)
                if 2**n<=int(S.prod(orders))*(K-1):continue
                tags=[[rng.randrange(o) for _ in range(n)] for o in orders];bins={}
                for x in product((0,1),repeat=n):
                    k=tuple(sum(a*b for a,b in zip(z,x))%o for z,o in zip(tags,orders));bins.setdefault(k,[]).append(x)
                W=next(v[:K] for v in bins.values() if len(v)>=K);F=trie_cnf(W,n)
                assert len(F)<=n*K
                actual={x for x in product((0,1),repeat=n) if all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F)}
                assert actual==set(W);source_checks+=1
                for z,o in zip(tags,orders):
                    c=Counter(sum(a*b for a,b in zip(z,x))%o for x in actual)
                    assert len(c)==1 and all(v%K==0 for v in c.values());blind_checks+=1
        for o in (1,3,7,13,15):
            counts=Counter(x%o for x in range(2**n));assert max(counts.values())==(2**n+o-1)//o;balance_checks+=1
    return dict(incidence=169,smith=snf,series=series_checks,derivative=derivative_checks,moments=moment_checks,transport=checks,poles=pole_checks,source=source_checks,blind=blind_checks,balanced=balance_checks)
if __name__=='__main__':print(run())
