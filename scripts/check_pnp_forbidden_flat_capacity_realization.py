"""Exact rank-two forbidden-flat realization in odd-capacity source geometry.

This is a reduction into the arbitrary-affine-demand screen contract, not a
claim that every such demand occurs on the original X3C continuation path.
"""
from check_pnp_affine_normal_components import canon, chart, lift, satisfies


def realize(n,F):
    """Each forbidden (a=alpha,b=beta) becomes three original incidence bits.
    The bits are complements of the two mismatches and their XOR.
    Their weight is 3 at the excluded corner and 1 everywhere else.
    """
    H=[];R=[];N=n
    for G in F:
        assert len(G)==2
        (a,alpha),(b,beta)=G
        assert 0<a<1<<n and 0<b<1<<n and alpha in (0,1) and beta in (0,1)
        r=0
        for p,s in ((a,1^alpha),(b,1^beta),(a^b,1^alpha^beta)):
            H.append(((1<<N)^p,s));r|=1<<N;N+=1
        R.append(r)
    H=canon(H)
    assert H is not None and canon(H+tuple((r,1) for r in R))==H
    return N,tuple(R),H,(1,)*len(R)


def nae_flat(l,m,k):
    """Literal representation (normal,offset), value dot(normal,z) XOR offset.
    NAE fails iff the first literal agrees with both other literals.
    """
    a,s=l;b,t=m;c,u=k
    return ((a^b,s^t),(a^c,s^u))


def reduce_3cnf(n,clauses):
    """NAE4(l,m,k,0) iff original clause. Split with one fresh t:
    NAE(l,m,t) and NAE(not t,k,0). Handles repeated literals too.
    Degenerate flats are permitted by realize if normals coincide; zero
    normals are avoided here by fresh t and using t as first argument.
    """
    F=[]
    for i,(l,m,k) in enumerate(clauses):
        t=(1<<(n+i),0)
        F.append(nae_flat(t,l,m))
        F.append(nae_flat((t[0],1),k,(0,0)))
    return realize(n+len(clauses),F)


def source_witness(N,H,z):
    u,V=chart(N,H)
    assert 0<=z<1<<len(V)
    return lift(u,V,z)


def extend_3cnf(n,clauses,z):
    """Construct the fresh NAE split choices for a satisfying assignment."""
    assert 0<=z<1<<n
    def val(l):
        a,b=l
        return ((a&z).bit_count()%2)^b
    y=z
    for i,(l,m,k) in enumerate(clauses):
        a,b,c=val(l),val(m),val(k)
        if not (a or b or c):return None
        # If a=b the first NAE forces t=not a. Otherwise choose t=0,
        # so not t=1 gives the second NAE both a 1 and its constant 0.
        t=1^a if a==b else 0
        y|=t<<(n+i)
    return y


def main():
    from itertools import product
    from random import Random
    from sympy import Matrix
    rng=Random(3692716);checks=0
    for d in range(2,7):
        for _ in range(50):
            F=tuple(tuple(zip(rng.sample(range(1,1<<d),2),
                (rng.randrange(2),rng.randrange(2)))) for j in range(rng.randrange(1,5)))
            N,R,H,caps=realize(d,F)
            A=Matrix(len(R),N,lambda i,j:R[i]>>j&1)
            for z in range(1<<d):
                y=source_witness(N,H,z)
                w=A*Matrix([y>>j&1 for j in range(N)])
                assert tuple(w)==tuple(1 if satisfies(z,(),(G,)) else 3 for G in F)
                assert satisfies(z,(),F)==all(v==1 for v in w)
                checks+=1
    for d in range(1,5):
        for _ in range(40):
            clauses=tuple(tuple((1<<rng.randrange(d),rng.randrange(2)) for j in range(3))
                          for i in range(rng.randrange(1,5)))
            N,R,H,caps=reduce_3cnf(d,clauses)
            for z in range(1<<d):
                want=all(any(((a&z).bit_count()%2)^b for a,b in C) for C in clauses)
                q=extend_3cnf(d,clauses,z)
                assert (q is not None)==want
                if q is not None:
                    y=source_witness(N,H,q)
                    assert all((r&y).bit_count()==1 for r in R)
                got=False
                for t in range(1<<len(clauses)):
                    y=source_witness(N,H,z|(t<<d))
                    ok=all((r&y).bit_count()==1 for r in R)
                    assert not ok or want
                    got|=ok
                assert got==want
                checks+=1
    print(dict(exact_checks=checks,controls='PASS'))

if __name__=='__main__':main()
