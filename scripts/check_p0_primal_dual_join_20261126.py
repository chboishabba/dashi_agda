"""Capped exact primal/dual CNF join; not a universal SAT algorithm."""
from random import Random
from check_p0_future_safe_affine_packet_20261125 import bits, plain, project, violate, reference, sat

class Exhausted(Exception): pass

class Budget:
    def __init__(self, limit): self.left = limit
    def pay(self, n=1):
        self.left -= n
        if self.left < 0: raise Exhausted

def mul(A, B, budget):
    out = set()
    for a in A:
        for b in B:
            budget.pay()
            out.symmetric_difference_update((a | b,))
    return out

def suffix_anf(f, budget):
    out = {0}
    for c in reversed(f):
        bad = {0}
        for l in c:
            b = 1 << (abs(l)-1)
            bad = mul(bad, {0,b} if l > 0 else {b}, budget)
        bad.symmetric_difference_update((0,))
        out = mul(out, bad, budget)
    return out

def join(n, rows, f, cut, budget):
    """Return full parity/marked packet; caller handles exhaustion separately."""
    budget.pay(n+len(rows)+len(f)+sum(map(len,f)))
    live = [0]*(len(f)+1)
    for j in range(len(f)-1,-1,-1):
        live[j] = live[j+1]
        for l in f[j]: live[j] |= 1 << (abs(l)-1)
    active = (1<<n)-1
    item = project(plain(rows), (1,)+tuple(1<<(i+1) for i in range(n)), active, live[0])
    S = {} if item is None else {item[0]:item[1]}
    for j in range(cut):
        T = {}
        for B,P in S.items():
            for R in (B, plain(B+violate(f[j]))):
                budget.pay()
                item = project(R,P,live[j],live[j+1])
                if item is None: continue
                K,V = item
                V = tuple(a^b for a,b in zip(T.get(K,(0,)*(n+1)),V))
                if any(V): T[K] = V
                else: T.pop(K,None)
        S = T
    if not S: return 0
    A = suffix_anf(f[cut:],budget)
    result = 0
    for B,P in S.items():
        for m in A:
            budget.pay()
            R = plain(B+tuple((1<<i,1) for i in bits(m)))
            item = project(R,P,live[cut],0)
            if item is not None: result ^= item[1][0]
    return result

def recover(n, rows, f, limit):
    """Polynomial-budget portfolio; None is UNKNOWN, never UNSAT."""
    allowance = limit//(len(f)+1)
    for cut in sorted(range(len(f)+1),key=lambda j:abs(2*j-len(f))):
        try: p = join(n,rows,f,cut,Budget(allowance))
        except Exhausted: continue
        if p&1:
            x = p>>1
            if sat(x,f) and all((a&x).bit_count()%2==b for a,b in rows): return x
        # An exact packet is independent of cut. No additional join can help.
        return None
    return None

def main():
    rng = Random(92); joins = singleton = 0
    for n in range(9):
        for _ in range(100):
            rows = tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            f = [tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(3,n)+1))) for _ in range(rng.randrange(9))]
            p,c = reference(n,rows,f)
            for cut in range(len(f)+1):
                assert join(n,rows,f,cut,Budget(1000000)) == p
                joins += 1
            if c==1:
                assert recover(n,rows,f,1000000)==p>>1
                singleton+=1
    # Full-degree suffix, sparse dual chart: one monomial, not all moments.
    for n in (16,32,64,128):
        f=[(i,) for i in range(1,n+1)]
        assert join(n,(),f,0,Budget(10000))==1|(((1<<n)-1)<<1)
        assert recover(n,(),f,0) is None
    # Zero packet can be inhabited; an odd packet need not be a witness.
    assert join(2,(),[],0,Budget(100))==0 and reference(2,(),[])[1]==4
    assert join(2,(),[(1,2)],0,Budget(100))==1 and recover(2,(),[(1,2)],100) is None
    print('exact joins',joins,'singleton recoveries',singleton,'high-degree controls 4, zero/odd controls PASS')
if __name__=='__main__': main()
