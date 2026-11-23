from itertools import product
from collections import Counter
import sympy as S
T=(-1,0,1)
def bt(x): return (x+1)%3-1
def enc(p):
 x,y,z=p; return x,bt(y-x),bt(z-x)
def dec(q):
 c,u,v=q; return c,bt(c+u),bt(c+v)
def rot(p): return p[1:]+p[:1]
def transport(q):
 c,u,v=q; return bt(c+u),bt(v-u),bt(-u)
P=list(product(T,repeat=3))
assert all(dec(enc(p))==p and enc(dec(p))==p for p in P)
assert all(enc(rot(p))==transport(enc(p)) for p in P)
assert all(enc(tuple(-x for x in p))==tuple(-x for x in enc(p)) for p in P)
assert set(Counter(enc(p)[1:] for p in P).values())=={3}
assert Counter(sum(p) for p in P)==dict(zip(range(-3,4),(1,3,6,7,6,3,1)))
assert all(Counter(bt(sum(p)) for p in P)[i]==9 for i in T)
R=S.Matrix([[0,1,0],[0,0,1],[1,0,0]])
N=R-S.eye(3); mod=lambda M:M.applyfunc(lambda x:x%3)
assert mod(N**3)==S.zeros(3) and mod(N**2)!=S.zeros(3)
assert mod(N**2)==S.ones(3)
assert all(not (a==b==c and (a+b+c)%3==1) for a,b,c in product(range(3),repeat=3))
# Preserve Euclidean signed lift of sum through mod-3 sheet and carry.
assert all(sum(p)==bt(sum(p))+3*((sum(p)-bt(sum(p)))//3) for p in P)
print('SymPy',S.__version__,'27 roundtrips / rotations / signs PASS; 9 fibres of 3; 3 modular sheets of 9; Euclidean slices 1,3,6,7,6,3,1; nilpotent flag PASS')
