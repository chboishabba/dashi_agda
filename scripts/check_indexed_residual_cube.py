from itertools import permutations, product
import sympy as s
x,y,z=s.symbols('x y z'); u=s.Matrix([x,y,z,1])
# Distinct vertex charts; each arrow is conjugated transport between charts.
V=list(product((0,1),repeat=3))
C={v:s.Matrix([[1,v[0],v[1],v[2]],[0,1,v[2],v[0]],[0,0,1,v[1]],[0,0,0,1]]) for v in V}
T=[s.eye(4) for _ in range(3)]
for i in range(3): T[i][i,3]=i+1
def step(v,i):
 w=tuple(a+(j==i) for j,a in enumerate(v)); return w,C[w]*T[i]*C[v].inv()
def path(v,order):
 M=s.eye(4)
 for i in order:
  v,N=step(v,i); M=N*M
 return M
faces=0
for v in V:
 for i,j in [(0,1),(0,2),(1,2)]:
  if v[i]==v[j]==0:
   assert path(v,(i,j))==path(v,(j,i)); faces+=1
P=[path((0,0,0),p) for p in permutations(range(3))]
assert all(M==P[0] for M in P)
# A noncommuting time/frame example: translation followed by rotation.
R=s.Matrix([[0,-1],[1,0]]); a=s.Matrix([1,0]); q=s.Matrix([x,y]); defect=R*(q+a)-(R*q+a)
assert defect==s.Matrix([-1,1]); assert R*q+a+defect==R*(q+a)
# Independent time-specific frames: conjugated prediction and residual.
r=s.Matrix(s.symbols('r0:2')); U0=s.eye(2); U1=R
assert U1*(q+a+r)==U1*(U0.inv()*U0*q+a)+U1*r
print(f'SymPy {s.__version__}: {faces}/6 faces; {len(P)}/6 endpoints; nonzero defect and reconstruction PASS; time-frame residual PASS')
