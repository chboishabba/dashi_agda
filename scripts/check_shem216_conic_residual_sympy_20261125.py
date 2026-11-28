# Independent exact SymPy replay: original finite field and retained 53 quotient.
from itertools import product
from collections import Counter
import sympy as sp
t=sp.symbols('t')
p=sp.Poly(t**3-t-1,t,modulus=3)
assert p.is_irreducible
def poly(x): return sp.Poly(sum(a*t**i for i,a in enumerate(x)),t,modulus=3)
def vec(p): return tuple(int(p.nth(i))%3 for i in range(3))
def mult(x,y): return vec((poly(x)*poly(y)).rem(p))
def power(x,n):
    z=(1,0,0)
    for _ in range(n): z=mult(z,x)
    return z
V=list(product(range(3),repeat=3)); zero=(0,0,0)
def canonical(v):
    return tuple((a*next(a for a in v if a))%3 for a in v)
axes=[v for v in V if v!=zero and canonical(v)==v]
def dot(a,b):return sum(x*y for x,y in zip(a,b))%3
lines=[{v for v in axes if dot(n,v)==0} for n in axes]
conics=[{canonical(power(v,25)) for v in l} for l in lines]
for n,c in zip(axes,conics):
    assert c=={v for v in axes if dot(n,mult(power(v,3),power(v,9)))==0}
    assert Counter(len(c&l) for l in lines)=={0:3,1:4,2:6}
    e=[(1,0,0),(0,1,0),(0,0,1)]
    Q=lambda v:dot(n,mult(power(v,3),power(v,9)))
    M=sp.Matrix(3,3,lambda i,j: (2*(Q(tuple((a+b)%3 for a,b in zip(e[i],e[j])))-Q(e[i])-Q(e[j])))%3)
    assert int(M.det())%3!=0
print("13/13 exact nonsingular conics; 169 line-conic intersections; per conic: 3 external, 4 tangent, 6 secant")
def p54(x):
 r,q,a,b=x
 return (q//4,r-1,a,b)
def pack(x):
 p,r,a,b=p54(x); k=x[1]%4
 return ((0,),k,p) if (r,a,b)==(0,0,0) else ((1,p,r,a,b),k,None)
def unpack(z):
 v,k,p=z
 if v==(0,): return (1,4*p+k,0,0)
 _,p,r,a,b=v
 return (r+1,4*p+k,a,b)
def apply(x,i):
 r,q,a,b=x
 if i==0: return (r,7-q,-a,-b) if r==1 else x
 if i==1: return (2-r,7-q,-a,-b)
 return (r,q^4,a,b)
def residual_action(z,i):
 v,k,p=z
 if v==(0,):
  return (v,3-k if i in (0,1) else k,1-p)
 _,p,r,a,b=v
 if i==0 and r!=0:return z
 if i==2:return ((1,1-p,r,a,b),k,None)
 return ((1,1-p,-r,-a,-b),3-k,None)
C=list(product(range(3),range(8),range(-1,2),range(-1,2)))
for x in C:
 assert unpack(pack(x))==x
 for i in range(3):
  assert pack(apply(x,i))==residual_action(pack(x),i)
  assert unpack(residual_action(pack(x),i))==apply(x,i)
print("216/216 exact retained quotient inverse; 648/648 residual action squares and inverse squares")
