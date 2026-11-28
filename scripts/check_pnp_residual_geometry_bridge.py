"""Source-order trellis, anchored consumer cuts and actual fraction valuation audit.
Scoped exact producers. Work counters are abstract, not standard-machine clocks.
"""
from itertools import product
from math import prod
from random import Random
from check_pnp_target_trellis import extend_rref, trellis
from check_pnp_stack_fractran import compile_stack, Runner

def ordered_trellis(F, cols, target, offset, R, cap):
    """Greedy exact cut capacity, then existing trellis on the same source.
    Return representatives in ORIGINAL R order; never interpret refusal as empty.
    """
    F, R = tuple(map(tuple,F)), tuple(R)
    n, m = len(R), len(target)
    if cap < 0 or len(set(R)) != n or any(not 0 <= i < len(cols) for i in R):
        raise ValueError("source/cap")
    if any(len(c) != m+1 for c in cols) or any(abs(l)-1 not in R for c in F for l in c):
        raise ValueError("source")
    work = 0
    def pay(k):
        nonlocal work
        if work+k > cap: raise OverflowError("order cap")
        work += k
    def rank_basis(indices):
        B = ()
        for i in indices:
            pay(12*(m+1)*(len(B)+1))
            B = extend_rref(B,tuple(v%3 for v in cols[i][:-1]))
        return B
    try:
        pay(1+len(cols)*(m+1)+n+sum(1+len(c) for c in F))
        supports = tuple(frozenset(abs(l)-1 for l in c) for c in F)
        rank = len(rank_basis(R))
        order, remaining, B, seen = [], list(R), (), set()
        peak = 1
        while remaining:
            best = None
            for i in remaining:
                pay(12*(m+1)*(len(B)+1)+n+sum(1+len(c) for c in F))
                C = extend_rref(B,tuple(v%3 for v in cols[i][:-1]))
                tail = [j for j in remaining if j != i]
                d = len(C)+len(rank_basis(tail))-rank
                cut = seen | {i}
                w = sum(bool(s & cut) and bool(s-cut) for s in supports)
                # charge construction/comparison of the integer score
                pay(1+4*(m+len(F)+1)**2)
                score = (3**d * 2**w, i)
                if best is None or score < best[0]:
                    best = score, C, tail, cut
            (size,i), B, remaining, seen = best
            order.append(i); peak = max(peak,size)
        pay(1+n*n)
    except OverflowError:
        return None,dict(order_work=work,work=work,stage="order",order=tuple())
    out, stats = trellis(F,cols,target,offset,order,cap-work)
    stats = dict(stats,order_work=work,work=work+stats["work"],order=tuple(order),predicted_peak=peak)
    if out is None: return None,stats
    H,P = out
    positions = {j:i for i,j in enumerate(order)}
    return (H,tuple(None if p is None else tuple(p[positions[j]] for j in R) for p in P)),stats

def anchored_move(x,d):
    """d=x-y, not an arbitrary displacement from x."""
    if len(x)!=len(d) or any(b not in (0,1) for b in x): raise ValueError("carrier")
    y = tuple((b-v)%3 for b,v in zip(x,d))
    return y if all(b in (0,1) for b in y) else None

def consumer_obligations(x, alternatives, state, consumer):
    """Explicit domain only. Quotient equal supports, remove dominated supersets.
    Not a polynomial producer of alternatives for arbitrary implicit SAT.
    """
    supports = set()
    for y in alternatives:
        if len(y)!=len(x): raise ValueError("carrier")
        if state(x)==state(y) and consumer(x)!=consumer(y):
            s = frozenset(i for i,(a,b) in enumerate(zip(x,y)) if a!=b)
            assert s
            supports.add(s)
    return tuple(s for s in sorted(supports,key=lambda s:(len(s),tuple(sorted(s))))
                 if not any(t<s for t in supports))

def sufficient_reads(supports,reads):
    return all(s.intersection(reads) for s in supports)

def valuation_bounds(primes,v):
    """Exact integer inequalities, no floating logs or giant materialization.
    Bounds on bit length of prod(p**e), assuming integer p>=2.
    """
    if len(primes)!=len(v) or any(p<2 for p in primes) or any(e<0 for e in v):
        raise ValueError("basis")
    lo = 1+sum((p.bit_length()-1)*e for p,e in zip(primes,v))
    hi = max(1,sum(p.bit_length()*e for p,e in zip(primes,v)))
    return lo,hi

def valuation_step(M,primes,v,cap=10000):
    """Check actual emitted fraction priority against literal integer FRACTRAN.
    Caller supplies distinct primes; reject oversized materialization.
    """
    if len(set(primes))!=len(primes): raise ValueError("basis")
    lo,hi = valuation_bounds(primes,v)
    if hi>cap: return None
    N = prod(p**e for p,e in zip(primes,v))
    assert lo<=N.bit_length()<=hi
    k,u = Runner(M).first(v)
    fractions = M.fractions(primes)
    j = next((j for j,f in enumerate(fractions) if N%f.denominator==0),None)
    assert k==j
    if j is not None:
        f=fractions[j]
        assert N//f.denominator*f.numerator==prod(p**e for p,e in zip(primes,u))
    return k,u

def main():
    if not __debug__: raise RuntimeError("assertions required")
    from sympy import prime
    g=Random(3692818)
    order_checks=anchor_checks=consumer_checks=valuation_checks=0
    for n in range(1,8):
        X=list(product((0,1),repeat=n))
        for _ in range(24):
            m=3
            cols=tuple(tuple(g.randrange(3) for _ in range(m+1)) for _ in X[0])
            t=tuple(g.randrange(3) for _ in range(m))
            F=tuple(tuple(g.choice((-1,1))*g.randrange(1,n+1) for _ in range(3)) for _ in range(n))
            R=tuple(reversed(range(n)))
            out,stats=ordered_trellis(F,cols,t,0,R,10**8)
            assert out is not None and stats["work"]<=10**8
            hist=[0]*3
            def valid(x):
                return all(any(x[abs(l)-1]==int(l>0) for l in c) for c in F) and all(sum(cols[i][j]*x[i] for i in range(n))%3==t[j] for j in range(m))
            for x in X:
                if valid(x): hist[sum(cols[i][-1]*x[i] for i in range(n))%3]+=1
            assert out[0]==tuple(hist)
            for k,p in enumerate(out[1]):
                assert (p is None)==(hist[k]==0)
                if p is not None:
                    x=tuple(p[R.index(i)] for i in range(n))
                    assert valid(x) and sum(cols[i][-1]*x[i] for i in range(n))%3==k
            assert ordered_trellis(F,cols,t,0,R,0)[0] is None
            order_checks+=1
        state=lambda x:sum(x)%3
        consumer=lambda x:sum((i+1)*b for i,b in enumerate(x))%3
        for x in X:
            S=consumer_obligations(x,X,state,consumer)
            for y in X:
                d=tuple((a-b)%3 for a,b in zip(x,y))
                assert anchored_move(x,d)==y
                anchor_checks+=1
            for z in X:
                R={i for i,b in enumerate(z) if b}
                assert sufficient_reads(S,R)==all(state(x)!=state(y) or consumer(x)==consumer(y) or any(x[i]!=y[i] for i in R) for y in X)
                consumer_checks+=1
    assert anchored_move((0,0),(1,2)) is None
    for _ in range(32):
        M=compile_stack(1,2,0,((0,1,0,0,g.choice((-1,0,1))),))
        v=M.encode(0,tuple(g.randrange(2) for _ in range(2)),(1,g.randrange(2)))
        primes=tuple(int(prime(i+1)) for i in range(len(v)))
        for _ in range(200):
            result=valuation_step(M,primes,v)
            assert result is not None
            k,u=result; valuation_checks+=1
            if k is None: break
            v=u
        else: raise AssertionError("finite control did not halt")
    # A compact exponent with 129 bits already requires exponentially
    # many bits in a materialized integer, regardless of macro count.
    assert valuation_bounds((2,),(2**128,))[0]==2**128+1
    print(dict(order=order_checks,anchored=anchor_checks,consumer=consumer_checks,valuation=valuation_checks))

if __name__=="__main__": main()
