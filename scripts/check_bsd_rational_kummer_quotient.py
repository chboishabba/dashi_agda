"""Finite group regression of the rational Kummer quotient proof.
These are not elliptic point groups or actual arithmetic H1 computations.
"""
from itertools import product
checks=0
def ck(ok):
    global checks
    if not ok: raise AssertionError('Kummer quotient guard failed')
    checks+=1
for N in (4,8,16,32,64):
    for a in range(N):
        if a*a%N!=1:continue
        fixed={p for p in range(N) if a*p%N==p}
        halves={p:[q for q in range(N) if 2*q%N==p] for p in fixed}
        if any(not q for q in halves.values()):continue
        torsion={0,N//2}
        delta=lambda q:(a-1)*q%N
        B={delta(q) for q in torsion}
        C={d for d in torsion if (a+1)*d%N==0}
        cls=lambda d:frozenset((d+b)%N for b in B)
        K={p:cls(delta(halves[p][0])) for p in fixed}
        doubles={2*p%N for p in fixed}
        for p in fixed:
            ck(all(delta(q) in C for q in halves[p]))
            ck(all(cls(delta(q))==K[p] for q in halves[p]))
            ck((K[p]==cls(0))==(p in doubles))
            for r in fixed:
                ck(K[(p+r)%N]==frozenset((x+y)%N for x,y in product(K[p],K[r])))
                ck((K[p]==K[r])==((p-r)%N in doubles))
        ck(len(set(K.values()))*len(doubles)==len(fixed))
        ck(set(K.values())=={cls(d) for d in C if d in {delta(q) for q in range(N)}})
print(f'{checks}/{checks} exact rational Kummer quotient controls PASS')
