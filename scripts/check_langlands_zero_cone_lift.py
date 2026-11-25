"""R399-R402: parsimonious bounded-occurrence zero-cone lift.
Exhaustive enumeration is confined to independent small reference tests.
"""
from collections import Counter
from itertools import product
from random import Random
from sympy import Matrix

BITS = tuple(product((0, 1), repeat=3))
BAD = tuple(b for b in BITS if b not in ((0, 0, 0), (1, 1, 0)))
ODD = tuple(b for b in BITS if sum(b) % 2)


def exclusion(vs, bits):
    return tuple(-v if b else v for v, b in zip(vs, bits))


def normalize(f, n):
    out = []
    for c in f:
        assert all(1 <= abs(l) <= n for l in c)
        c = tuple(sorted(set(c), key=lambda l: (abs(l), l)))
        if any(-l in c for l in c):
            continue
        assert len(c) <= 3
        out.append(c)
    return out


def lift(f, n):
    """All clauses have 3 distinct variables, each variable occurs <=11 times.
    For n>=1 and no empty clause. Original coordinates are retained by map.
    """
    f = normalize(f, n)
    assert n >= 1 and all(f)
    groups = [[] for _ in range(n)]
    main = []
    count = 0
    for c in f:
        cc = []
        for l in c:
            i = abs(l)-1
            groups[i].append(count)
            cc.append((count, l > 0))
            count += 1
        main.append(cc)
    for g in groups:
        if not g:
            g.append(count); count += 1
    if count == 1:
        groups[0].append(count); count += 1
    def x(j): return 3*j+1
    def z(j): return 3*j+3
    gadget = []
    for j in range(count):
        gadget.extend(exclusion((x(j), x(j)+1, z(j)), b) for b in BAD)
    external = []
    for cc in main:
        c = [x(j) if sign else -x(j) for j, sign in cc]
        j = cc[0][0]
        if len(c) < 3:
            c.append(z(j))
        if len(c) < 3:
            c.append(z((j+1) % count))
        external.append(tuple(c))
    for g in groups:
        for a,b in zip(g,g[1:]):
            external.extend(((-x(a), x(b), z(a)), (x(a), -x(b), z(a))))
    return tuple(gadget+external), groups, tuple(external)


def reopen(bits, groups):
    return tuple(bits[3*g[0]] for g in groups)


def extend(bits, groups):
    out = [None]*(3*sum(map(len, groups)))
    for b,g in zip(bits, groups):
        for j in g:
            out[3*j:3*j+3] = [b,b,0]
    assert None not in out
    return tuple(out)


def sat(f, bits):
    return all(any(bits[abs(l)-1] == int(l>0) for l in c) for c in f)


def rowsum(f, N):
    s = [0]*N
    for c in f:
        for l in c: s[abs(l)-1] += 1 if l>0 else -1
    return s


def certificate(f, groups, external):
    """Positive integer kernel vector for original signed incidence rows."""
    N = 3*sum(map(len, groups))
    # Baseline: weight 1 on every clause, correct each triple with odd-parity rows.
    s = rowsum(f, N)
    y = [4]*len(f)
    for j in range(N//3):
        u = s[3*j:3*j+3]
        B = 1+sum(map(abs,u))
        for i,b in enumerate(BAD):
            if b in ODD:
                r = [1-2*t for t in b]
                y[6*j+i] += 4*B-sum(a*c for a,c in zip(u,r))
    total = [0]*N
    for c,w in zip(f,y):
        assert w > 0
        for l in c: total[abs(l)-1] += w*(1 if l>0 else -1)
    assert not any(total)
    assert len(f) == 6*(N//3)+len(external)
    assert all(len(c)==len(set(map(abs,c)))==3 for c in f)
    assert max(Counter(abs(l) for c in f for l in c).values()) <= 11
    return y


def moment(ws, tags, mod):
    result = 0
    for b in ws:
        w=1
        for x,z in zip(b,tags):
            if x: w=w*z%mod
        result=(result+w)%mod
    return result


def baseline(tags, mod):
    a=1
    for z in tags: a=a*(1+z)%mod
    return a


def main():
    R=Matrix([[1-2*b for b in row] for row in ODD])
    assert R.T*R==4*Matrix.eye(3) and R.T*Matrix.ones(4,1)==Matrix.zeros(3,1)
    local=[b for b in BITS if sat([exclusion((1,2,3),a) for a in BAD],b)]
    assert local==[(0,0,0),(1,1,0)]
    rng=Random(399); cases=small=roundtrips=weighted=hall=0; kinds=Counter()
    fixtures=[(1,()),(1,((1,),)),(1,((-1,),)),(2,((1,),(-1,),)),(2,((1,2),)),(2,((1,-1),)),(2,((1,1),))]
    for n in range(1,7):
        for _ in range(40):
            f=tuple(tuple(rng.choice((-1,1))*j for j in rng.sample(range(1,n+1),rng.randint(1,min(3,n)))) for _ in range(rng.randrange(0,3*n+1)))
            fixtures.append((n,f))
    for n,f in fixtures:
        F,G,E=lift(f,n); N=3*sum(map(len,G)); certificate(F,G,E)
        xs=list(product((0,1),repeat=n)); ws=[b for b in xs if sat(f,b)]
        lifted=[extend(b,G) for b in ws]
        for b in xs:
            t=extend(b,G); assert reopen(t,G)==b and sat(F,t)==sat(f,b); roundtrips+=1
        # Check all gadget-allowed choices (one bit per occurrence copy), not all 3N bits.
        k=N//3
        if k<=10:
            seen=[]
            for a in product((0,1),repeat=k):
                t=tuple(q for b in a for q in (b,b,0))
                if sat(F,t): seen.append(t)
            assert set(seen)==set(lifted); small+=1
        if N<=9:
            assert {t for t in product((0,1),repeat=N) if sat(F,t)}==set(lifted)
            for mask in range(1,1<<N):
                S={i+1 for i in range(N) if mask>>i&1}
                assert sum(any(abs(l) in S for l in c) for c in F)>=2*len(S); hall+=1
        m=1<<(n+4); tags=[pow(5,1<<i,1<<(n+2)) for i in range(n)]; lifted_tags=[1]*N
        for z,g in zip(tags,G): lifted_tags[3*g[0]]=z
        A=baseline(tags,m); B=baseline(lifted_tags,m)
        D=(3*A-4*moment(ws,tags,m))%m; L=(3*B-4*moment(lifted,lifted_tags,m))%m
        assert D==(L-3*(B-A))%m; weighted+=1
        kinds['empty' if not ws else 'singleton' if len(ws)==1 else 'multi']+=1; cases+=1
    for n in (32,128,512):
        f=[(i if rng.randrange(2) else -i,) for i in range(1,n+1)]
        F,G,E=lift(f,n); N=3*sum(map(len,G)); certificate(F,G,E)
        b=tuple(int(c[0]>0) for c in f); assert sat(F,extend(b,G)) and reopen(extend(b,G),G)==b
    print(dict(cases=cases, classes=dict(kinds), original_roundtrips=roundtrips, independent_copy_enumerations=small, strict_hall_checks=hall, weighted_spectral_transports=weighted, large_structural_lifts=3))


if __name__=='__main__': main()
