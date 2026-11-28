"""Capped affine resolvent producer; random visibility, exact decisions, original verification."""
from itertools import combinations
from random import Random, SystemRandom
from check_langlands_adaptive_spectral_producer import Field, affine_chart
from check_p0_future_safe_affine_packet_20261125 import plain, violate, sat, reference, bits
from check_p0_affine_coface_20261125 import coface
from check_p0_primal_dual_join_20261126 import Budget, Exhausted, suffix_anf
from check_p0_strict_selector_20261126 import reverse_estimate


def inv(K, a, budget):
    if not a: raise ZeroDivisionError
    u,v=a,K.mod; g,h=1,0
    while u != 1:
        budget.pay()
        j=u.bit_length()-v.bit_length()
        if j<0: u,v=v,u; g,h=h,g; j=-j
        u^=v<<j; g^=h<<j
    while g.bit_length()>K.m:
        budget.pay(); g^=K.mod<<(g.bit_length()-K.m-1)
    return g


def fibre(K,n,B,z,budget):
    """L_V(z+a0) and L'_V, without forming the degree-2^d polynomial."""
    budget.pay(n+len(B)+1)
    base,V=affine_chart(n,B)
    t=z^(1<<n)^base; c=1
    for i,v in enumerate(V):
        budget.pay(3)
        assert v
        t=K.mul(t,t)^K.mul(v,t); c=K.mul(v,c)
        for j in range(i+1,len(V)):
            budget.pay(2); w=V[j]; V[j]=K.mul(w,w)^K.mul(v,w)
    assert t and c
    budget.pay(); return K.mul(c,inv(K,t,budget))


def toggle(S,B):
    if B is not None: S.symmetric_difference_update((B,))


def compress(S,n,budget):
    P=(1,)+(0,)*n
    while True:
        for A,B in combinations(sorted(S),2):
            budget.pay(); q=coface(A,P,B,P)
            if q is None: continue
            H,R,_=q; assert R==P
            S.remove(A); S.remove(B); toggle(S,H); break
        else: return S


def compile_cut(n,rows,f,cut,budget):
    budget.pay(n+len(rows)+len(f)+sum(map(len,f)))
    S=set(); toggle(S,plain(rows))
    for clause in f[:cut]:
        T=set(S)
        for B in S:
            budget.pay(); toggle(T,plain(B+violate(clause)))
        S=compress(T,n,budget)
    if not S: return S
    A=suffix_anf(f[cut:],budget); T=set()
    for B in S:
        for mask in A:
            budget.pay(); toggle(T,plain(B+tuple((1<<i,1) for i in bits(mask))))
    return compress(T,n,budget)


def restrict_chart(S,i,b,n,budget):
    T=set()
    for B in S:
        budget.pay(); toggle(T,plain(B+((1<<i,b),)))
    return compress(T,n,budget)


def observe(K,n,S,z,budget):
    v=0
    for B in S: v^=fibre(K,n,B,z,budget)
    return v


def valid(x,n,rows,f):
    return 0<=x<1<<n and sat(x,f) and all((a&x).bit_count()%2==b for a,b in rows)


def recover(n,rows,f,cap,security=16,rng=None):
    """Cap covers all compilation attempts and descent; None is UNKNOWN."""
    assert security>=1
    rng=SystemRandom() if rng is None else rng
    budget=Budget(cap//2)
    per=(cap-cap//2)//(len(f)+1)
    for cut in sorted(range(len(f)+1),key=lambda j:abs(2*j-len(f))):
        try: S=compile_cut(n,rows,f,cut,Budget(per)); break
        except Exhausted: continue
    else: return None
    if not S: return None
    try:
        budget.pay(n+security+len(rows)+len(f)+sum(map(len,f)))
        if len(S)==1:
            x,_=affine_chart(n,next(iter(S)))
            return x if valid(x,n,rows,f) else None
        K=Field(n+security); budget.pay(K.m)
        # Fixed number of independent random bits, always outside all labels.
        z=(1<<(K.m-1))|rng.getrandbits(K.m-1)
        value=observe(K,n,S,z,budget)
        if not value: return None
        x=0
        for i in range(n):
            T=restrict_chart(S,i,0,n,budget); q=observe(K,n,T,z,budget)
            b=int(q==0); h=reverse_estimate(n,b); assert int(h<0)==b
            if b: S=restrict_chart(S,i,1,n,budget); x|=1<<i
            else: S=T; value=q
            assert value
        return x if valid(x,n,rows,f) else None
    except Exhausted: return None


def oracle(K,n,rows,f,z):
    v=0
    for x in range(1<<n):
        if valid(x,n,rows,f): v^=inv(K,z^(1<<n)^x,Budget(100000))
    return v


def main():
    from sympy import Poly, Symbol
    rng=Random(95); charts=cuts=descents=inhabited=0; t=Symbol('t')
    for n in range(8):
        K=Field(n+4); h=K.m//2
        assert Poly(t**(2*h)+t**h+1,t,modulus=2).is_irreducible
        for _ in range(40):
            rows=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for _ in range(rng.randrange(6))]
            z=(1<<(K.m-1))|rng.getrandbits(K.m-1); B=plain(rows)
            if B is not None:
                assert fibre(K,n,B,z,Budget(100000))==oracle(K,n,rows,[],z); charts+=1
            want=oracle(K,n,rows,f,z)
            for cut in range(len(f)+1):
                S=compile_cut(n,rows,f,cut,Budget(100000))
                assert observe(K,n,S,z,Budget(100000))==want; cuts+=1
            _,c=reference(n,rows,f); inhabited+=bool(c)
            x=recover(n,rows,f,2000000,16,rng)
            if x is not None: assert c and valid(x,n,rows,f); descents+=1
            if not c: assert x is None
    # An exponential-index observation in polynomial field operations.
    for n in (16,32,64,128,256):
        K=Field(n+4); z=1<<(K.m-1); budget=Budget(3*n*n+10000)
        assert fibre(K,n,(),z,budget)!=0
        assert recover(n,(),[],100000,16,rng)==0
    # Exact partition of a full affine fibre, and cancellation of identical supports.
    K=Field(10); z=1<<(K.m-1); b=Budget(100000)
    assert fibre(K,8,(),z,b)==fibre(K,8,((1,0),),z,b)^fibre(K,8,((1,1),),z,b)
    assert compress({(),((1,0),),((1,1),)},8,b)==set()
    assert recover(8,(),[(1,),(-1,)],100000,16,rng) is None
    assert recover(8,(),[],0,16,rng) is None
    print(dict(fields=8,affine_charts=charts,cut_comparisons=cuts,inhabited=inhabited,verified=descents,large_controls=5,controls='PASS'))


if __name__=='__main__': main()
