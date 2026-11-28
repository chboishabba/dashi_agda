from itertools import product
from sympy import Poly, symbols, GF, __version__
t=symbols('t'); f=Poly(t**3-t-1,t,modulus=3)
assert f.is_irreducible
P=list(product(range(3),repeat=3))
def mul(a,b):
    q=(Poly(sum(x*t**i for i,x in enumerate(a)),t,modulus=3)*Poly(sum(x*t**i for i,x in enumerate(b)),t,modulus=3)).rem(f)
    return tuple(int(q.nth(i))%3 for i in range(3))
zero=(0,0,0); one=(1,0,0); gen=(0,1,0)
p=[one]
for _ in range(13):p.append(mul(p[-1],gen))
assert len(set(p[:-1]))==13 and p[-1]==one
inv={a:next(b for b in P if mul(a,b)==one) if a!=zero else zero for a in P}
G=[tuple(mul(tuple(s*x%3 for x in q),inv[a] if e else a) for a in P) for q in p[:-1] for s in (1,2) for e in (0,1)]
assert len(set(G))==52
idx={x:i for i,x in enumerate(P)}
for g in G:
    assert g[idx[zero]]==zero and len(set(g))==27
    for h in G: assert tuple(g[idx[x]] for x in h) in G
w=lambda a:sum(x!=0 for x in a)
for a,b in product(P,repeat=2):
    assert min(w(tuple((u-v)%3 for u,v in zip(b,g[idx[a]]))) for g in G)==(w(b) if a==zero else 1 if b==zero else 0)
print(__version__, '52 distinct permutations; 2704 closure and 729 minimum support checks PASS')
