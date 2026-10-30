#!/usr/bin/env python3
"""M13 two-case interval partition oracle: bounded one-period vs crossing.
Exactly compares numeric index lists and formal log(p)log(q) monomials.
Source-written Agda may still need kernel checking; not an analytic proof.
"""
from random import Random
from collections import Counter
from math import isqrt

def prime_power_base(n):
    if n < 2: return None
    for p in range(2, isqrt(n)+1):
        if n % p == 0:
            q = n
            while q % p == 0: q //= p
            return p if q == 1 else None
    return n

def monomial(n):
    a,b=prime_power_base(n),prime_power_base(n+2)
    return (a,b) if a is not None and b is not None else None

def two_case(start,count):
    rem=start%270
    if rem+count <= 270:
        return "within", [270*((start+i)//270)+(start+i)%270 for i in range(count)]
    prefix=270-rem
    first=start//270+1
    blocks,suffix=divmod(count-prefix,270)
    assert start+prefix==270*first
    assert count==prefix+270*blocks+suffix
    return "cross", (
        list(range(start,start+prefix))+
        [270*k+r for k in range(first,first+blocks) for r in range(270)]+
        list(range(270*(first+blocks),270*(first+blocks)+suffix)))

def main():
    rng=Random(11917)
    cases=[(59,1),(59,2),(269,1),(269,2),(270,0),(270,270),
           (270,271),(0,271),(329,1),(329,999)]
    cases += [(rng.randrange(30000),rng.randrange(1250)) for _ in range(3000)]
    counts={"within":0,"cross":0}
    symbolic=0
    for idx,(start,count) in enumerate(cases):
        kind,sequence=two_case(start,count)
        assert sequence == list(range(start,start+count))
        counts[kind]+=1
        if idx%11 == 0:
            expected=Counter(w for n in range(start,start+count)
                             if (w:=monomial(n)) is not None)
            actual=Counter(w for n in sequence
                           if (w:=monomial(n)) is not None)
            assert expected==actual
            symbolic+=1
    print({"status":"PASS","total":len(cases),"branches":counts,
           "symbolic_log_pair_checks":symbolic,
           "agda_kernel_checked":False,"analytic_bound_proved":False})
if __name__ == "__main__":
    main()
