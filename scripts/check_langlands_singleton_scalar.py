"""R391-R394: actual rank-two trace, packed singleton decoder, scoped tests.
The exhaustive producer is a reference only, never part of the decoder.
"""
from itertools import product
from random import Random
import sympy as s


def chart(n):
    """Return tag integers and the modulus for the signed first coefficient."""
    if n < 0:
        raise ValueError('negative arity')
    m = 1 << (n + 2)
    return [pow(5, 1 << i, m) for i in range(n)], 4*m


def baseline(tags, modulus):
    a = 1
    for z in tags:
        a = a*(1+z) % modulus
    return a


def recover_moment(d, n):
    tags, modulus = chart(n)
    delta = (3*baseline(tags, modulus)-d) % modulus
    if delta % 4:
        return None
    return delta//4


def decode(d, n):
    """Decode a supplied residue; None = no candidate, not an UNSAT proof."""
    w = recover_moment(d, n)
    if w is None or w % 4 != 1:
        return None
    a = 0
    for i in range(n):
        # Compare modulo 2^(i+3), where 5 has order 2^(i+1).
        m = 1 << (i+3)
        if pow(5, a, m) != w % m:
            a += 1 << i
        if pow(5, a, m) != w % m:
            return None
    if pow(5, a, 1 << (n+2)) != w:
        return None
    return tuple((a >> i)&1 for i in range(n))


def satisfies(f, x):
    return all(any(x[abs(l)-1] == int(l>0) for l in c) for c in f)


def verified_candidate(f, n, d):
    x = decode(d,n)
    return x if x is not None and satisfies(f,x) else None


def ref_signed_trace(n, witnesses):
    tags, modulus = chart(n)
    a = baseline(tags, modulus)
    w = sum(pow(5, sum(bit << i for i,bit in enumerate(x)), modulus//4)
            for x in witnesses)
    return (3*a-4*w)%modulus


def main():
    # Original Q3 S3 standard U, Frobenius identity; inertia character inner products.
    r=s.Matrix([[0,-1],[1,-1]]); t=s.Matrix([[0,1],[1,0]])
    assert r**3==t**2==s.eye(2) and t*r*t==r.inv()
    group=[r**i*t**j for i in range(3) for j in range(2)]
    assert sum(g.trace() for g in group)==0
    assert sum(g.trace()*g.inv().trace() for g in group)==6
    E=s.zeros(4)
    for g in group:
        E += s.kronecker_product(g,g.inv().T)/6
    assert E*E==E and E.rank()==1
    count=0
    for n in range(13):
        tags, mod=chart(n)
        assert len(set(pow(5,a,mod//4) for a in range(1<<n)))==1<<n
        for i in range(n):
            assert pow(5,1<<i,1<<(i+3))==1+(1<<(i+2))
        assert decode(ref_signed_trace(n,[]),n) is None
        for x in product((0,1),repeat=n):
            d=ref_signed_trace(n,[x])
            assert decode(d,n)==x
            count+=1
    # Direct rank-two determinant first coefficient on actual invariant factors.
    T=s.Symbol('T'); spectral=0
    for z,b in product([1,5,9,13,17],[0,1]):
        poly=s.Poly((1-z*T)**(3-2*b)*(1+z*T)**(2*b),T)
        assert -poly.nth(1)==(3-4*b)*z
        spectral+=1
    rng=Random(391); cases=0; unique=0; empty=0; multi=0; collisions=0
    for n in range(1,9):
        for _ in range(80):
            f=[tuple(rng.choice((-1,1))*j for j in rng.sample(range(1,n+1),rng.randint(1,min(n,3)))) for _ in range(rng.randrange(0,4*n+1))]
            ws=[x for x in product((0,1),repeat=n) if satisfies(f,x)]
            d=ref_signed_trace(n,ws); x=verified_candidate(f,n,d)
            if not ws:
                assert x is None; empty+=1
            elif len(ws)==1:
                assert x==ws[0]; unique+=1
            else:
                assert x is None or x in ws; multi+=1
            cases+=1
    # Occupied-zero and false-candidate controls on actual CNF support.
    n=3; xs=list(product((0,1),repeat=n)); d0=ref_signed_trace(n,[])
    false_candidates=0
    for mask in range(1,1<<len(xs)):
        ws=[x for i,x in enumerate(xs) if mask>>i&1]
        d=ref_signed_trace(n,ws)
        f=[tuple(j+1 if bit==0 else -(j+1) for j,bit in enumerate(x)) for x in xs if x not in ws]
        assert [x for x in xs if satisfies(f,x)]==ws
        if d==d0:
            collisions+=1
            assert verified_candidate(f,n,d) is None
        x=decode(d,n)
        if x is not None and x not in ws:
            false_candidates+=1
            assert verified_candidate(f,n,d) is None
    assert collisions>0 and false_candidates>0
    precision=0
    for n in range(1,65):
        x=(0,)*n; y=(0,)*(n-1)+(1,)
        _,mod=chart(n)
        assert ref_signed_trace(n,[x])% (mod//2)==ref_signed_trace(n,[y])%(mod//2)
        assert ref_signed_trace(n,[x])!=ref_signed_trace(n,[y])
        precision+=1
    large=0
    for n in (32,64,128,256,512):
        for _ in range(5):
            x=tuple(rng.randrange(2) for _ in range(n))
            assert decode(ref_signed_trace(n,[x]),n)==x
            large+=1
    # Padding pins the low exponents; low residue bits then encode the full count.
    padding=0
    for n in range(1,9):
        for _ in range(16):
            f=[tuple(rng.choice((-1,1))*j for j in rng.sample(range(1,n+1),rng.randint(1,min(n,3)))) for _ in range(rng.randrange(0,3*n+1))]
            ws=[x for x in product((0,1),repeat=n) if satisfies(f,x)]
            shifted=[tuple((abs(l)+n)*(1 if l>0 else -1) for l in c) for c in f]
            padded=[(-j,) for j in range(1,n+1)]+shifted
            if n<=4:
                assert [x for x in product((0,1),repeat=2*n) if satisfies(padded,x)]==[(0,)*n+x for x in ws]
            d=ref_signed_trace(2*n,[(0,)*n+x for x in ws])
            assert recover_moment(d,2*n)%(1<<(n+2))==len(ws)
            padding+=1
    print(dict(singleton_roundtrips=count,empty_controls=13,spectral_blocks=spectral,
               cnfs=cases,unique=unique,empty=empty,multi=multi,occupied_zero=collisions,false_candidates=false_candidates,
               precision=precision,large_roundtrips=large,padded_counts=padding))


if __name__=='__main__':
    main()
