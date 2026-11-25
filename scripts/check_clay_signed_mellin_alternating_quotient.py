"""Finite exact controls for the signed Mellin and alternating quotient lemmas.
Not a computation of an actual newform's zero divisor or a Chow group.
"""
from itertools import permutations
from collections import Counter
import sympy as s

checks = 0
def check(ok):
    global checks
    if not ok:
        raise AssertionError('exact check failed')
    checks += 1

x = s.symbols('x')
# Sharp model: shifted Legendre polynomial has m simple roots in (0,1),
# m vanishing moments and a strictly positive first surviving moment.
# These are signed-measure fixtures in x, not elliptic-curve L-functions.
for m in range(13):
    p = s.Poly(s.legendre(m, 2*x-1), x)
    check(p.degree() == m and p.LC() > 0)
    check(p.count_roots(0, 1) == m)
    for j in range(m+1):
        v = s.integrate(p.as_expr()*x**j, (x, 0, 1))
        check(v == (0 if j < m else s.factorial(m)**2/s.factorial(2*m+1)))
    check(s.integrate(p.as_expr()**2, (x, 0, 1)) == s.Rational(1,2*m+1))

# Exact group algebra at m=2..6: alternating projector, even-quotient
# trace and ordinary symmetric-quotient annihilation. Use integer numerators.
def sign(p):
    return (-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))
def mul(p,q):
    return tuple(p[i] for i in q)
for m in range(2,7):
    G = list(permutations(range(m)))
    sig = {p:sign(p) for p in G}
    A = [p for p in G if sig[p]==1]
    check(2*len(A)==len(G))
    # Verify sign homomorphism on generators, not just cardinalities.
    for i in range(m-1):
        t=list(range(m));t[i],t[i+1]=t[i+1],t[i];t=tuple(t)
        check(all(sig[mul(t,p)] == -sig[p] for p in G))
    even_trace = Counter(); full_trace = Counter()
    for p in G:
        for q in G:
            v=mul(p,q)
            full_trace[v] += sig[p]
            if sig[q]==1: even_trace[v] += sig[p]
    check(all(even_trace[p] == len(A)*sig[p] for p in G))
    check(all(full_trace[p] == 0 for p in G))
    # Any partial diagonal is fixed pointwise by the swapped labels.
    for i in range(m):
        for j in range(i+1,m):
            t=list(range(m));t[i],t[j]=t[j],t[i];t=tuple(t)
            check(sig[t]==-1)
            labels=list(range(m));labels[j]=labels[i]
            check(tuple(labels[k] for k in t)==tuple(labels))
print(f'{checks}/{checks} exact checks PASS')
