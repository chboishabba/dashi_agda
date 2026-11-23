import numpy as np
import sympy as s
from itertools import product, permutations, combinations
x=s.symbols('x'); f=s.Poly(x**9+x**4-1,x,modulus=3)
def vec(p): return [int(p.nth(i))%3 for i in range(9)]
a=s.Poly(x**5,x,modulus=3); cols=[]
for i in range(9):
 cols.append(vec(a)); a=(a**3).rem(f)
B=s.Matrix(cols).T; D=B.inv_mod(3)
assert (B*D).applyfunc(lambda x:x%3)==s.eye(9)
B=np.array(B,dtype=np.int64); D=np.array(D,dtype=np.int64)
X=np.array(list(product(range(3),repeat=9)),dtype=np.int64)
order=[0,3,6,1,4,7,2,5,8]; M=B[:,order]; N=D[order,:]
assert np.array_equal((X@M.T@N.T)%3,X)
rot=[1,2,0,4,5,3,7,8,6]
P=np.eye(9,dtype=np.int64)[rot]; F=(M@P@N)%3
def fp(p):
 for _ in range(6): p=(p**3).rem(f)
 return p
Factual=np.array([vec(fp(s.Poly(x**i,x,modulus=3))) for i in range(9)]).T
assert np.array_equal(F,Factual)
assert np.array_equal((X[:,rot]@M.T)%3,(X@M.T@F.T)%3)
# Vertex metadata identifies split and encoding stage. Full word retained.
def pack(v):
 b=(v+1)%3-1; return (b!=0).astype(int),b
def unpack(p):
 mask,b=p; assert np.array_equal(mask,b!=0); return b%3
def E(v,word):
 c=unpack(word) if v[2] else word
 return (c@M.T)%3
def J(v,z):
 c=(z@N.T)%3
 return pack(c) if v[2] else c
def edge(v,z,i):
 u=list(v);u[i]=1;u=tuple(u)
 w=J(v,z); c=unpack(w) if v[2] else w
 if i==1:c=c[:,rot]
 w=pack(c) if u[2] else c
 return E(u,w),u
for v in product((0,1),repeat=3):
 free=[i for i in range(3) if not v[i]]
 for i,j in combinations(free,2):
  z=E(v,pack(X) if v[2] else X); a,u=edge(v,z,i);a,_=edge(u,a,j);b,u=edge(v,z,j);b,_=edge(u,b,i)
  assert np.array_equal(a,b)
for p in permutations(range(3)):
 v=(0,0,0); z=E(v,X)
 for i in p:z,v=edge(v,z,i)
 assert np.array_equal(unpack(J(v,z)),X[:,rot])
print('SymPy',s.__version__,'states',len(X),'six faces and six terminal paths',6*len(X),'each; actual Frobenius^6 direction PASS')
