"""Paper 9 strict contrast -> Section92 parity consumer; capped, never UNSAT."""
from fractions import Fraction as Q
from random import Random
from check_p0_primal_dual_join_20261126 import Budget, Exhausted, join
from check_p0_future_safe_affine_packet_20261125 import reference, sat


def reverse_estimate(n, child):
    assert n >= 1 and child in (0, 1)
    return Q(1 if child == 0 else -1, 1 << (n+1))


def from_packet(p, i):
    b = (p >> (i+1)) & 1
    a = (p & 1) ^ b
    return 0 if a else (1 if b else None)


def packet(n, rows, f, allowance):
    # Each cut attempt gets its own share; all attempts together <= allowance.
    for j in sorted(range(len(f)+1), key=lambda j: abs(2*j-len(f))):
        try:
            return join(n, rows, f, j, Budget(allowance//(len(f)+1)))
        except Exhausted:
            continue
    return None


def select(n, rows, f, i, allowance):
    """Return strict rational estimate or UNKNOWN. i is an original index."""
    assert 0 <= i < n
    per = allowance//3
    p = packet(n, rows, f, per)
    if p is not None:
        b = from_packet(p,i)
        if b is not None:
            return reverse_estimate(n,b)
    # Nonzero child packet (not just scalar odd) certifies inhabited support.
    for b in (0,1):
        q = packet(n, rows+((1<<i,b),), f, per)
        if q:
            return reverse_estimate(n,b)
    return None


def recover(n, rows, f, allowance):
    """Fixed original-coordinate self-reduction, with total charged cap."""
    x = 0
    pins = tuple(rows)
    for i in range(n):
        h = select(n,pins,f,i,allowance//max(1,n))
        if h is None:
            return None
        b = int(h < 0)
        x |= b<<i
        pins += ((1<<i,b),)
    return x if sat(x,f) and all((a&x).bit_count()%2==b for a,b in rows) else None


def main():
    pairs = 0
    for n in range(1,9):
        for a in range((1<<n)+1):
            for b in range((1<<n)-a+1):
                if not a+b: continue
                d = Q(a-b,a+b)
                for k,c in enumerate((a,b)):
                    if c: assert abs(reverse_estimate(n,k)-d)<1
                pairs += 1
    assert abs(Q(0)-Q(-1))==1
    rng=Random(93)
    probes = recovered = odd = fixtures = 0
    for n in range(1,8):
        for _ in range(100):
            rows=tuple((rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(n+1)))
            f=[tuple(rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(min(n,3)+1))) for _ in range(rng.randrange(8))]
            p,c=reference(n,rows,f); fixtures+=1
            for i in range(n):
                h=select(n,rows,f,i,300000)
                a=reference(n,rows+((1<<i,0),),f)[1]
                b=reference(n,rows+((1<<i,1),),f)[1]
                assert a+b==c
                if h is not None:
                    assert c and abs(h-Q(a-b,c))<1 and (b if h<0 else a)>0
                    probes+=1
                if c%2: assert h is not None
            x=recover(n,rows,f,3000000)
            if c%2: assert x is not None; odd+=1
            if x is not None:
                assert c and sat(x,f) and all((a&x).bit_count()%2==b for a,b in rows)
                recovered+=1
    # Three satisfying models have invalid marked XOR but valid odd-child descent.
    assert reference(2,(),[(1,2)])==(1,3)
    assert recover(2,(),[(1,2)],10000) in (1,2,3)
    # Even parent and both even children, but child marked packets can be nonzero.
    assert reference(2,(),[])==(0,4)
    assert select(2,(),[],0,10000) is not None
    # Zero packet does not certify absence; 3-cube has zero child packets too.
    assert select(3,(),[],0,10000) is None
    assert recover(2,(),[(1,2)],0) is None
    assert select(1,(),[()],0,10000) is None
    print(dict(count_pairs=pairs,fixtures=fixtures,sound_estimates=probes,verified_recoveries=recovered,odd_sources_recovered=odd,controls='PASS'))


if __name__=='__main__': main()
