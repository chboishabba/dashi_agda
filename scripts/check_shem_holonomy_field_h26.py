from sympy import Poly, symbols
from itertools import product
from collections import Counter
x=symbols('x'); p=Poly(x**3-x-1,x,modulus=3); assert p.is_irreducible
V=list(product(range(3),repeat=3)); zero=(0,0,0); one=(1,0,0)
def add(a,b):return tuple((i+j)%3 for i,j in zip(a,b))
def neg(a):return tuple(-i%3 for i in a)
def mul(a,b):
 q=(Poly(sum(a[i]*x**i for i in range(3)),x,modulus=3)*Poly(sum(b[i]*x**i for i in range(3)),x,modulus=3)).rem(p)
 return tuple(int(q.nth(i))%3 for i in range(3))
M={(a,b):mul(a,b) for a in V for b in V}; I={a:next(b for b in V if M[a,b]==one) if a!=zero else zero for a in V}
frames=list(product(V,V[1:])); assert len(frames)==702
# Canonical physical chart transport: conjugation by independently known affine frame.
def en(f,r):return add(f[0],M[f[1],r])
def de(f,y):return M[I[f[1]],add(y,neg(f[0]))]
# All frames and all states, then all pairs of frames around root with canonical loop.
for f in frames:
 for r in V:assert de(f,en(f,r))==r
fixed=Counter(); checks=0
for f in frames:
 H={r:en(f,I[de(f,r)]) for r in V}
 assert all(H[H[r]]==r for r in V)
 fixed[sum(H[r]==r for r in V)]+=1
 for r in V:assert H[r]==r if de(f,r) in (zero,one,neg(one)) else H[r]!=r
 checks+=27
# Pure gauge and loop with one inversion via arbitrary pair; root is identity.
for f in frames:
 for r in V:
  assert en(f,de(f,r))==r
print('frames',len(frames),'roundtrips',len(frames)*27*2,'twisted loop states',checks,'fixed counts',dict(fixed))
