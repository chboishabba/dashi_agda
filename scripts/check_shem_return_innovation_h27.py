from sympy import Poly, symbols, __version__
from itertools import product
x=symbols('x'); p=Poly(x**3-x-1,x,modulus=3); assert p.is_irreducible
V=list(product(range(3),repeat=3)); zero=(0,0,0); one=(1,0,0)
def add(a,b):return tuple((i+j)%3 for i,j in zip(a,b))
def sub(a,b):return tuple((i-j)%3 for i,j in zip(a,b))
def mul(a,b):
 q=(Poly(sum(a[i]*x**i for i in range(3)),x,modulus=3)*Poly(sum(b[i]*x**i for i in range(3)),x,modulus=3)).rem(p)
 return tuple(int(q.nth(i))%3 for i in range(3))
M={(a,b):mul(a,b) for a in V for b in V}; I={a:next(b for b in V if M[a,b]==one) if a!=zero else zero for a in V}
frames=list(product(V,V[1:])); assert len(frames)==702
def en(f,r):return add(f[0],M[f[1],r])
def de(f,y):return M[I[f[1]],sub(y,f[0])]
for f in frames:
 for r in V:
  assert de(f,en(f,r))==r and en(f,de(f,r))==r
  assert (en(f,I[de(f,r)])==r)==(de(f,r) in (zero,one,sub(zero,one)))
# The current visit, previous state and signed innovation form a reversible update.
for prev,delta in product(V,repeat=2):
 current=add(prev,delta)
 assert sub(current,prev)==delta and sub(current,delta)==prev
# Physical return change with independent source/target frames: check all
# frame pairs and all states using lookup tables rather than repeated SymPy calls.
E=[[en(f,r) for r in V] for f in frames]; D=[[V.index(de(f,r)) for r in V] for f in frames]; E=[[V.index(v) for v in row] for row in E]
for i,j in product(range(len(frames)),repeat=2):
 for k in range(27):assert D[i][E[j][D[j][E[i][k]]]]==k
print('SymPy',__version__,'field irreducible; chart roundtrips',702*27*2,'twisted states',702*27,'time-innovation inverse checks',27*27*2,'physical return inverses',702*702*27)
