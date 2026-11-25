"""Fast-pi inspired exact projective signed child counts; capped, not universal SAT."""
from math import gcd
from itertools import combinations
from random import Random
from check_p0_future_safe_affine_packet_20261125 import canon, plain, violate, sat, reference
from check_p0_primal_dual_join_20261126 import Budget, Exhausted
from check_p0_strict_selector_20261126 import reverse_estimate
from check_p0_affine_coface_20261125 import coface


def add(S, B, w):
    if B is not None and w:
        v = S.get(B, 0) + w
        if v: S[B] = v
        else: S.pop(B, None)


def retire(B, w, active, keep):
    if B is None: return None, 0
    dead = active & ~keep
    R = canon(B, dead)
    free = dead.bit_count() - sum(bool(dead >> i & 1) for i, a, b in R)
    return plain(tuple((a,b) for i,a,b in R if not (dead >> i & 1))), w << free


def simplify(S, n, budget):
    # Geometry is donated by the binary coface owner; integer signs are separate.
    P = (1,) + (0,)*n
    while True:
        for A,B in combinations(S,2):
            budget.pay()
            a,b = S[A],S[B]
            if not (a == b or a == -b): continue
            q = coface(A,P,B,P)
            if q is None: continue
            H,_,kind = q
            if kind == 'siblings' and a == b: w = a
            elif kind == 'nested' and a == -b: w = a if len(A)<len(B) else b
            else: continue
            del S[A]; del S[B]; add(S,H,w)
            break
        else: return


def normalize(S, budget):
    g = 0
    for w in S.values():
        budget.pay(); g = gcd(g,abs(w))
    if g > 1:
        for B in S:
            budget.pay(); S[B] //= g
    return max(1,g)


def child_pair(n, rows, f, i, budget):
    """Return (positive common scale, normalized child counts), or raise Exhausted."""
    assert 0 <= i < n
    budget.pay(n+len(rows)+len(f)+sum(map(len,f))+sum(a.bit_count() for a,b in rows))
    live = [1<<i]*(len(f)+1)
    for j in range(len(f)-1,-1,-1):
        live[j] = live[j+1]
        for l in f[j]: live[j] |= 1<<(abs(l)-1)
    S = {}
    B,w = retire(plain(rows),1,(1<<n)-1,live[0]); add(S,B,w)
    scale = normalize(S,budget)
    for j,c in enumerate(f):
        T = {}
        for B,w in S.items():
            budget.pay(2)
            for R,v in ((B,w),(plain(B+violate(c)),-w)):
                K,z = retire(R,v,live[j],live[j+1]); add(T,K,z)
        simplify(T,n,budget)
        scale *= normalize(T,budget)
        S = T
    counts=[]
    for b in (0,1):
        total=0
        for B,w in S.items():
            budget.pay()
            R=plain(B+((1<<i,b),))
            if R is not None: total += w
        assert total>=0
        counts.append(total)
    return scale,tuple(counts)


def select(n, rows, f, i, allowance):
    try: _,(a,b) = child_pair(n,rows,f,i,Budget(allowance))
    except Exhausted: return None
    return reverse_estimate(n,0 if a else 1) if a or b else None


def recover(n, rows, f, allowance):
    x=0; pins=tuple(rows)
    for i in range(n):
        h=select(n,pins,f,i,allowance//max(1,n))
        if h is None: return None
        b=int(h<0); x|=b<<i; pins+=((1<<i,b),)
    return x if sat(x,f) and all((a&x).bit_count()%2==b for a,b in rows) else None


def main():
    rng=Random(94); fixtures=checks=inhabited=even=0
    for n in range(1,8):
        for _ in range(100):
            rows=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for _ in range(rng.randrange(8))]
            _,c=reference(n,rows,f); fixtures+=1
            for i in range(n):
                g,ab=child_pair(n,rows,f,i,Budget(1000000))
                assert tuple(g*v for v in ab)==tuple(reference(n,rows+((1<<i,b),),f)[1] for b in (0,1))
                checks+=1
            x=recover(n,rows,f,10000000)
            assert (x is not None)==bool(c)
            inhabited+=bool(c); even+=bool(c and not c%2)
    for n in (16,32,64,128):
        g,ab=child_pair(n,(),[],0,Budget(10000)); assert g==1<<(n-1) and ab==(1,1)
        f=[(-i,) for i in range(1,n+1)]+[(-i,i%n+1) for i in range(1,n+1)]
        assert child_pair(n,(),f,0,Budget(100000))==(1,(1,0))
    assert select(3,(),[],0,0) is None
    assert select(3,(),[()],0,10000) is None
    print(dict(fixtures=fixtures,child_pairs=checks,verified=inhabited,even_verified=even,stress=8,controls='PASS'))


if __name__=='__main__': main()
