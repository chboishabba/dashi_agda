from collections import Counter
from itertools import product
from random import Random
from sympy import Matrix, eye, zeros, Rational, kronecker_product, primerange

q = 3
R = Matrix([[-1,-1],[1,0]])
J = Matrix([[0,1],[1,0]])
reps = [(eye(1),eye(1)),(eye(1),-eye(1)),(R,J)]

def chain(k):
    return Matrix(k,k,lambda i,j:int(j==i+1))

# Independently compute inertia-invariant Hom using actual S3 generators.
inertia = 0
for i,j in product(range(3),repeat=2):
    A,B = reps[i],reps[j]
    d,e = A[0].rows,B[0].rows
    M = Matrix.vstack(*[kronecker_product(eye(e),a)-kronecker_product(b.T,eye(d)) for a,b in zip(A,B)])
    assert d*e-M.rank()==int(i==j)
    inertia += 1

# Compute the kernel of N_k X-X N_l on each exact Phi weight space.
# Vectorization uses column-major order. No assumed chain decomposition.
chains = weights = 0
for k,l in product(range(1,8),repeat=2):
    M=kronecker_product(eye(l),chain(k))-kronecker_product(chain(l).T,eye(k))
    expected=Counter(range(-(l-1),min(k,l)-(l-1)))
    actual=Counter()
    for h in range(1-l,k):
        cols=[j*k+i for j in range(l) for i in range(k) if i-j==h]
        dim=len(cols)-M[:,cols].rank()
        if dim: actual[h]=dim
        assert dim==expected[h]
        weights+=1
    assert actual==expected and k*l-M.rank()==min(k,l)
    P=Matrix.diag(*[q**i for i in range(k)])
    assert P*chain(k)*P.inv()==chain(k)/q
    chains+=1

# Actual pole multiplicities by explicit block-pair summation; tags are exponents
# modulo odd m, signs are separate, and slopes are integer q-exponents.
def poles(A,B,m):
    C=Counter()
    for (t,sg,k),v in A.items():
        for (u,sh,l),w in B.items():
            for j in range(min(k,l)):
                C[((u-t)%m,sg^sh,l-1-j)]+=v*w
    return C

def block(data,m,zero=False):
    # U-isotypic part of B_b; the trivial part cancels in four corners.
    C=Counter()
    for tag,k,b in data:
        b=0 if zero else b
        C[tag%m,0,k]+=3-2*b
        C[tag%m,1,k]+=2*b
    return +C

def tails(data,m,L):
    return Counter((tag%m,r) for tag,k,b in data if b for r in range(1,k+1))

rng=Random(235)
fixtures=shifted=gram=reverse=aligned=0
for _ in range(120):
    m=rng.choice([3,5,7,13]); L=5
    F=[(rng.randrange(m),rng.randint(1,L),rng.randrange(2)) for x in range(rng.randint(0,14))]
    G=[(rng.randrange(m),rng.randint(1,L),rng.randrange(2)) for x in range(rng.randint(0,14))]
    A,B,A0,B0=block(F,m),block(G,m),block(F,m,True),block(G,m,True)
    P,Q,V,Z=poles(A,B,m),poles(A,B0,m),poles(A0,B,m),poles(A0,B0,m)
    TF,TG=tails(F,m,L),tails(G,m,L)
    for c in range(m):
        K=0
        for s in range(L):
            want=8*sum(b*d for t,k,b in F for u,l,d in G if (u-t)%m==c and 0<=l-1-s<min(k,l))
            for sign in range(2):
                key=(c,sign,s)
                got=P[key]-Q[key]-V[key]+Z[key]
                assert got==(-1)**sign*want
                shifted+=1
            K+=want
        assert K==8*sum(TF[t,r]*TG[(t+c)%m,r] for t in range(m) for r in range(1,L+1))
        gram+=1
    for t,r in product(range(m),range(1,L+1)):
        probe=Counter({(0,0,r):1})
        # twist exponent -t; slope zero sees precisely chains >= r.
        assert poles(A,probe,m)[(-t%m,1,0)]==2*TF[t,r]
        assert TF[t,r]-TF[t,r+1]==sum(b for u,k,b in F if u==t and k==r)
        reverse+=1
    for f,g in zip(F,G):
        a,b,a0,b0=block([f],m),block([g],m),block([f],m,True),block([g],m,True)
        p,z,v,w=poles(a,b,m),poles(a,b0,m),poles(a0,b,m),poles(a0,b0,m)
        c=(g[0]-f[0])%m
        assert sum(p[c,0,s]-z[c,0,s]-v[c,0,s]+w[c,0,s] for s in range(L))==8*f[2]*g[2]*min(f[1],g[1])
        aligned+=1
    fixtures+=1

# Source-derived parity packets stratified by chain length: use actual
# bucket sums, tail differencing and injective-prime CRT (known support only).
from sympy import symbols, Poly
from sympy.ntheory.modular import crt
X=symbols('X')
crt_cases=crt_coeffs=0
for _ in range(36):
    n=8; L=4
    support={a:rng.randint(1,L) for a in rng.sample(range(1<<n),rng.randint(0,8))}
    primes=list(primerange(3,400))
    packets={}
    for p in primes:
        layers=[set() for r in range(L+1)]
        for a,k in support.items():
            for r in range(1,k+1): layers[r].symmetric_difference_update([a%p])
        packets[p]=layers
    m=max(len(layers[1]) for layers in packets.values())
    assert m==len(support)
    good=[p for p in primes if len(packets[p][1])==m]
    assert all(len({a%p for a in support})==m for p in good)
    for k in range(1,L+1):
        roots=[a for a,r in support.items() if r==k]
        polys=[]
        for p in good:
            rs=packets[p][k] ^ (packets[p][k+1] if k<L else set())
            f=Poly(1,X,modulus=p)
            for r in rs: f*=Poly(X-r,X,modulus=p)
            polys.append(f.all_coeffs())
        coeffs=[int(crt(good,cs,symmetric=True)[0]) for cs in zip(*polys)]
        f=Poly.from_list(coeffs,X)
        assert sorted(f.ground_roots())==sorted(roots) and f.degree()==len(roots)
        crt_coeffs+=len(coeffs)
    crt_cases+=1
print(dict(inertia=inertia,chains=chains,weights=weights,fixtures=fixtures,shifted=shifted,gram=gram,reverse=reverse,aligned=aligned,crt_cases=crt_cases,crt_coeffs=crt_coeffs))

# Nonunit Frobenius parameters: consecutive-probe quotient cancels all
# earlier layers even if q-slopes of distinct base tags coincide.
quotients=0
for _ in range(180):
    data=[(rng.randint(-4,4),rng.randint(1,6),rng.randint(1,3)) for x in range(rng.randint(0,18))]
    def spectrum(l):
        C=Counter()
        for a,k,v in data:
            for j in range(min(k,l)): C[a+j-l+1]+=v
        return C
    for l in range(1,7):
        current=spectrum(l)
        previous=Counter({a-1:v for a,v in spectrum(l-1).items()})
        expected=Counter()
        for a,k,v in data:
            if k>=l: expected[a]+=v
        current.subtract(previous)
        assert all(v>=0 for v in current.values()) and +current==expected
        quotients+=1
print(dict(nonunit_probe_quotients=quotients))
