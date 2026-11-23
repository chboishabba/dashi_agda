from itertools import permutations,product
import sympy as s
from sympy.polys.galoistools import gf_irreducible_p
from sympy.polys.domains import ZZ
# A: signed proper rotations of three-coordinate frame
rots=[]
for p in permutations(range(3)):
 for signs in product((-1,1),repeat=3):
  R=s.zeros(3)
  for i,j in enumerate(p):R[i,j]=signs[i]
  if R.det()==1:rots.append(R)
keys={tuple(r) for r in rots}
assert len(keys)==24
assert all(tuple(r*t) in keys for r in rots for t in rots)
assert all(r.T*r==s.eye(3) for r in rots)
# C: selected finite extension, relative Frobenius and normal basis
x=s.symbols('x'); f=s.Poly(x**9+x**4-1,x,modulus=3)
assert gf_irreducible_p([int(v)%3 for v in f.all_coeffs()],3,ZZ)
def mul(a,b):return (a*b).rem(f)
def power(a,n):
 r=s.Poly(1,x,modulus=3)
 while n:
  if n&1:r=mul(r,a)
  a=mul(a,a);n//=2
 return r
def vec(a):return s.Matrix([int(a.nth(i))%3 for i in range(9)])
a=s.Poly(x**5,x,modulus=3); basis=[power(a,3**i) for i in range(9)]
B=s.Matrix.hstack(*map(vec,basis)); assert int(B.det())%3!=0
F=s.Matrix.hstack(*(vec(power(s.Poly(x**i,x,modulus=3),27)) for i in range(9)))
mod=lambda a:a.applyfunc(lambda v:int(v)%3)
assert mod(F**3)==s.eye(9)
P=s.zeros(9)
for i in range(9):P[(i+3)%9,i]=1
assert mod(F*B-B*P)==s.zeros(9)
assert sum(all((int(v)%3)==0 for v in (F-s.eye(9))*s.Matrix(a)) for a in product(range(3),repeat=9))==27
print('SymPy',s.__version__,'A: 24 proper frames / 576 compositions PASS; C: irreducible modulus, normal basis, relative Frobenius intertwiner and 27 fixed points PASS')
