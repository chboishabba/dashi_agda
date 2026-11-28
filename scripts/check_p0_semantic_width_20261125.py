"""Section 77: exact future classes, dead reference and sparse support bound."""
from random import Random


def accepts(F,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in F)


def residual(F,n,d,p):
    return sum(1<<y for y in range(1<<(n-d)) if accepts(F,p|(y<<d)))


def split(t,r,b):
    return sum(((t>>(2*y+b))&1)<<y for y in range(1<<(r-1)))


def guarded(F,n):
    return [(1,)]+[tuple((abs(l)+1)*(1 if l>0 else -1) for l in c) for c in F],n+1


def recover_with_equal(F,n,equal):
    G,N=guarded(F,n);p=1;queries=0
    for d in range(2,N+1):
        dead=0
        if equal(G,N,d,p,dead):p|=1<<(d-1)
        queries+=1
    x=p>>1
    return (x if accepts(F,x) else None),queries


def sparse_messages(n,S):
    return [{p:tuple(sorted(x>>d for x in S if x&((1<<d)-1)==p)) for p in {x&((1<<d)-1) for x in S}} for d in range(n+1)]


def main():
    rng=Random(77);fixtures=layers=edges=equal_queries=singletons=empty=0
    for n in range(1,8):
        for _ in range(40):
            F=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(4))) for _ in range(rng.randrange(15))]
            S=[x for x in range(1<<n) if accepts(F,x)];M=sparse_messages(n,S)
            for d in range(n+1):
                T=[residual(F,n,d,p) for p in range(1<<d)]
                assert len(set(T))<=len(S)+1
                if len(S)==1:assert len(set(T))<=2
                for p,t in enumerate(T):
                    assert t==sum(1<<y for y in M[d].get(p,()))
                    if d<n:
                        for b in (0,1):
                            assert split(t,n-d,b)==residual(F,n,d+1,p|(b<<d));edges+=1
                layers+=1
            def eq(G,N,d,p,q):return residual(G,N,d,p)==residual(G,N,d,q)
            x,q=recover_with_equal(F,n,eq);equal_queries+=q
            assert (x is None)==(not S)
            if x is not None:assert x in S
            singletons+=len(S)==1;empty+=not S;fixtures+=1
    print(dict(fixtures=fixtures,layers=layers,transitions=edges,equality_queries=equal_queries,singletons=singletons,empty=empty))
    # Connected original equality system with a common hub clause on suffix bits.
    # Equality constraints imply y=x; the OR hub excludes only all-zero.
    for m in range(2,9):
        F=[c for i in range(1,m+1) for c in ((-i,m+i),(i,-(m+i)))]+[tuple(range(m+1,2*m+1))]
        T={residual(F,2*m,m,p) for p in range(1<<m)}
        assert len(T)==1<<m and 0 in T
    print('connected equality cut widths',[1<<m for m in range(2,9)])
    # A large sparse support ledger is built from supplied witnesses only.
    for n in (64,128,256,512):
        S=[(1<<n)-1];M=sparse_messages(n,S)
        assert len(M)==n+1 and all(len(t)==1 for t in M)
        assert all(t[(1<<d)-1]==((1<<(n-d))-1,) for d,t in enumerate(M))
    print('supplied singleton sparse ledger dimensions',64,128,256,512)


if __name__=='__main__':main()
