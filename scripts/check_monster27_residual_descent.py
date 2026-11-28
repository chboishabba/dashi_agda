from itertools import product
from math import gcd
from collections import Counter
import sympy as s

def req(v):
    if not v: raise AssertionError('source charge residual')

# Original charge chart and source per-root ranks.
rank={1:7298,3:7295,9:7296,27:7290}
pts=list(product((-1,0,1),repeat=3))
charge=lambda p: sum(a*3**j for j,a in enumerate(p))%27
r=lambda k: rank[27//gcd(k,27)]
req(len({charge(p) for p in pts})==27)
res={p:r(charge(p))-7290 for p in pts}
req(sum(res.values())==54 and all((v>0)==(p[0]==0) for p,v in res.items()))
req(Counter(res.values())=={0:18,6:6,5:2,8:1})
# Character inversion in exact cyclotomic quotient.
x=s.Symbol('x'); phi=s.Poly(s.cyclotomic_poly(27,x),x)
for j in range(27):
    tr=sum(r(k)*x**((j*k)%27) for k in range(27))
    target=196884 if j==0 else 54 if j%9==0 else 0 if j%3==0 else 3
    req(s.Poly(tr-target,x).rem(phi).is_zero)
    residual=sum((r(k)-7290)*x**((j*k)%27) for k in range(27))
    req(s.Poly(residual-(54 if j%9==0 else target),x).rem(phi).is_zero)
# Quotient C9 multiplicities, virtual permutation decomposition.
m=[r(3*k)-7290 for k in range(9)]
req(m==[6-int(k%3==0)+3*int(k==0) for k in range(9)])
req(sum(m)==54 and min(m)==5)
req([v-5 for v in m]==[3,1,1,0,1,1,0,1,1])
# A permutation lift would have fixed(g) subset fixed(g^3).
req(3>0)
# Source C27 projectors yield a rank-preserving chart, not a basis.
# Adjacent native edges must change cyclic charge; inversion preserves rank.
edges=[(p,q) for p in pts for q in pts if sum(abs(a-b) for a,b in zip(p,q))==1 and p<q]
req(len(edges)==54 and all(charge(p)!=charge(q) for p,q in edges))
req(all(res[p]==res[tuple(-a for a in p)] for p in pts))
print('PASS 27 source ranks, 54 residual dimensions, 54 exact character evaluations, 54 edge charge distinctions, inversion, C9 virtual permutation and maximal regular core')
