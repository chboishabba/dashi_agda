"""R403-R406: parsimonious tetrahedral parity lift and global Gram obstruction.
Exact local moments; exhaustive reference tests only on small inputs.
"""
from itertools import product
from collections import Counter, defaultdict
from random import Random
import sympy as s

BITS = tuple(product((0, 1), repeat=3))


def forbid(vs, b):
    return tuple(-v if t else v for v, t in zip(vs, b))


def parity(vs, rhs=0):
    return [forbid(vs, b) for b in BITS if sum(b) % 2 != rhs]


def sat(f, b):
    return all(any(b[abs(l)-1] == int(l > 0) for l in c) for c in f)


def lift(f, n):
    groups = [[] for _ in range(n)]
    main = []
    k = 0
    for c in f:
        c = sorted(set(c), key=lambda l: (abs(l), l))
        if any(-l in c for l in c):
            continue
        assert 0 < len(c) <= 3 and all(1 <= abs(l) <= n for l in c)
        row = []
        for l in c:
            groups[abs(l)-1].append(k)
            row.append((k, l > 0)); k += 1
        main.append(row)
    for g in groups:
        if not g:
            g.append(k); k += 1
    if k == 1:
        groups[0].append(k); k += 1
    def x(j): return 4*j+1
    def w(j): return 4*j+4
    F = []
    for j in range(k):
        a = x(j); d = w(j)
        for vs in ((a,a+1,d),(a,a+2,d),(a+1,a+2,d)):
            F.extend(parity(vs))
    for g in groups:
        for a,b in zip(g,g[1:]):
            F.extend(parity((x(a),x(b),w(a))))
    for row in main:
        c = [x(j) if b else -x(j) for j,b in row]
        j = row[0][0]
        if len(c)<3: c.append(w(j))
        if len(c)<3: c.append(w((j+1)%k))
        F.append(tuple(c))
    return F, groups, k


def extend(b, groups, k):
    out = [None]*(4*k)
    for bit,g in zip(b,groups):
        for j in g: out[4*j:4*j+4]=[bit,bit,bit,0]
    assert None not in out
    return tuple(out)


def reopen(b, groups):
    return tuple(b[4*g[0]] for g in groups)


def local_gram(F, N):
    # The global moment matrix is I_(N+1), never allocate it densely.
    scopes = defaultdict(list)
    for c in F:
        assert len(c)==3 and len(set(map(abs,c)))==3
        scopes[tuple(sorted(map(abs,c)))].append(c)
    assert max(Counter(abs(l) for c in F for l in c).values())<=18
    for vs,cs in scopes.items():
        idx = {v:i for i,v in enumerate(vs)}
        allowed = [b for b in BITS if all(any(b[idx[abs(l)]]==int(l>0) for l in c) for c in cs)]
        tetra = next((t for rhs in (0,1) if len(t:=[b for b in allowed if sum(b)%2==rhs])==4),None)
        assert tetra is not None and len(cs) in (1,4)
        spins = [(1,)+tuple(1-2*t for t in b) for b in tetra]
        assert all(sum(a[i]*a[j] for a in spins)==4*int(i==j) for i in range(4) for j in range(4))
    return len(scopes)


def moment(bs,tags,mod):
    result=0
    for b in bs:
        w=1
        for t,z in zip(b,tags):
            if t: w=w*z%mod
        result=(result+w)%mod
    return result


def baseline(tags,mod):
    a=1
    for z in tags: a=a*(1+z)%mod
    return a


def main():
    for rhs in (0,1):
        R=s.Matrix([[1-2*t for t in b] for b in BITS if sum(b)%2==rhs])
        assert R.T*R==4*s.eye(3) and R.T*s.ones(4,1)==s.zeros(3,1)
        H=R*R.T-3*s.ones(4,4)
        assert H==4*s.eye(4)-4*s.ones(4,4) and H.eigenvals()=={4:3,-12:1}
    # Local Walsh kernel: exact degree <=2 moment map and missing-corner recovery.
    V=s.Matrix([[s.prod(1-2*b[i] for i in I) for b in BITS] for I in ((),(0,),(1,),(2,),(0,1),(0,2),(1,2))])
    p=s.Matrix([(-1)**sum(b) for b in BITS])
    assert V.rank()==7 and V*p==s.zeros(7,1)
    assert all(V[:,[j for j in range(8) if j!=i]].det()!=0 for i in range(8))
    gadget=sum((parity(vs) for vs in ((1,2,4),(1,3,4),(2,3,4))),[])
    assert [b for b in product((0,1),repeat=4) if sat(gadget,b)]==[(0,0,0,0),(1,1,1,0)]
    # Local support can be recovered from pair moments and a specified forbidden vertex.
    rng=Random(403); walsh=0
    for i,b in enumerate(BITS):
        for _ in range(20):
            m=[rng.randrange(5) if j!=i else 0 for j in range(8)]
            if not sum(m): m[(i+1)%8]=1
            mu=s.Matrix(m)/sum(m); v=V*mu; B=V.T*v
            c=-p[i]*B[i]
            assert (B+c*p)/8==mu; walsh+=1
    fixtures=[(1,()),(1,((1,),)),(1,((-1,),)),(1,((1,),(-1,))), (2,((1,1),(-2,2))), (2,((1,2),))]
    for n in range(1,7):
        for _ in range(30):
            f=tuple(tuple(rng.choice((-1,1))*j for j in rng.sample(range(1,n+1),rng.randint(1,min(3,n)))) for _ in range(rng.randrange(0,3*n+1)))
            fixtures.append((n,f))
    kinds=Counter(); rounds=small=full=hall=grams=weighted=0
    for n,f in fixtures:
        F,G,k=lift(f,n); N=4*k; grams+=local_gram(F,N)
        xs=list(product((0,1),repeat=n)); ws=[b for b in xs if sat(f,b)]
        lifted=[extend(b,G,k) for b in ws]
        for b in xs:
            t=extend(b,G,k); assert reopen(t,G)==b and sat(F,t)==sat(f,b); rounds+=1
        if k<=9:
            seen=[]
            for a in product((0,1),repeat=k):
                t=tuple(q for b in a for q in (b,b,b,0))
                if sat(F,t): seen.append(t)
            assert set(seen)==set(lifted); small+=1
        if N<=8:
            assert {t for t in product((0,1),repeat=N) if sat(F,t)}==set(lifted); full+=1
            for mask in range(1,1<<N):
                S={i+1 for i in range(N) if mask>>i&1}
                assert sum(any(abs(l) in S for l in c) for c in F)>=3*len(S); hall+=1
        m=1<<(n+4); tags=[pow(5,1<<i,1<<(n+2)) for i in range(n)]; Z=[1]*N
        for z,g in zip(tags,G): Z[4*g[0]]=z
        A=baseline(tags,m); B=baseline(Z,m)
        D=(3*A-4*moment(ws,tags,m))%m; L=(3*B-4*moment(lifted,Z,m))%m
        assert D==(L-3*(B-A))%m; weighted+=1
        kinds['empty' if not ws else 'singleton' if len(ws)==1 else 'multi']+=1
    for n in (32,128,512):
        f=[(i if rng.randrange(2) else -i,) for i in range(1,n+1)]
        F,G,k=lift(f,n); grams+=local_gram(F,4*k)
        b=tuple(int(c[0]>0) for c in f); assert sat(F,extend(b,G,k))
    print(dict(original_cases=len(fixtures),classes=dict(kinds),roundtrips=rounds,copy_enumerations=small,full_lift_enumerations=full,hall_checks=hall,local_gram_scopes=grams,weighted_transports=weighted,walsh_reconstructions=walsh,large_lifts=3))


if __name__=='__main__': main()
