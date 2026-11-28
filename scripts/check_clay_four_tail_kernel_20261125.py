"""Exact finite controls; not numerical zero, PDE, Selmer or Chow proofs."""
from fractions import Fraction as Q
from itertools import permutations, product, combinations
import sympy as S

def need(b):
    if not b: raise ArithmeticError('regression failed')

# RH: exact triangular second difference on signed rational offsets.
pos=lambda x:max(x,0)
for j in range(-200,201):
    x=Q(j,100)
    need(pos(x+1)-2*pos(x)+pos(x-1)==pos(1-abs(x)))
y=S.symbols('y', positive=True)
need(S.expand(4*(y+1/y-2)-4*(y-1)**2/y)==0)
print('RH 401 triangular controls; principal exponential identity')

# BSD: original S3 permutation lattice kernel, retain ramified action.
G=list(permutations(range(3))); e=G[0]; a=(1,2,0); b=(1,0,2); r=(0,2,1)
def mul(g,h):return tuple(g[h[i]] for i in range(3))
def cos(H):return sorted(set(tuple(sorted(mul(g,h) for h in H)) for g in G))
C3=cos([e,a,mul(a,a)]); C2=cos([e,b]); A=S.zeros(8)
for j,g in enumerate(G):
    A[next(i for i,c in enumerate(C3) if g in c),j]=1
    A[2+next(i for i,c in enumerate(C2) if g in c),j]=1
    A[5+next(i for i,c in enumerate(C2) if mul(g,r) in c),j]=1
for i in range(2): A[i,6]=1
for i in range(2,5): A[i,7]=1
need(A.det()==18)
def act(g,v):
    inv=tuple(g.index(i) for i in range(3))
    return tuple(v[G.index(mul(inv,h))] for h in G)+tuple(v[6:])
mod=lambda v,p:tuple(int(x)%p for x in v)
u=(1,1,1,1,1,1,1,0); v=(1,2,2,1,1,2,0,0); w=(1,0,1,0,2,2,0,1)
K2={mod(S.Matrix(u)*i,2) for i in range(2)}
K3={mod(S.Matrix(v)*i+S.Matrix(w)*j,3) for i,j in product(range(3),repeat=2)}
rows=[list(map(int,A.row(i))) for i in range(8)]
for p,K in [(2,K2),(3,K3)]:
    actual={x for x in product(range(p),repeat=8) if all(sum(a*b for a,b in zip(row,x))%p==0 for row in rows)}
    need(actual==K)
    for g,x in product(G,K): need(act(g,x) in K)
need(all(act(g,u)==u for g in G))
need(act(a,v)==v and mod(act(b,v),3)==mod(-S.Matrix(v),3))
need(act(b,w)==w)
need(mod(act(a,w),3)==mod(S.Matrix(w)+S.Matrix(v),3))
need(not any(act(a,x)==x and x[7]==1 for x in K3))
print('BSD 256+6561 kernel enumeration, 66 action controls, non-split C3 unipotent action')

# NS: exact dyadic weights in the all-replacement and tail estimates.
for j in range(1,65):
    R=2**j
    need(sum(Q((2**k)**2,R**2) for k in range(j+1))<Q(4,3))
    need(sum(Q(R**2,(2**k)**2) for k in range(j,j+65))<Q(4,3))
    need(sum((2**k)**Q(5,2) for k in range(j+1))<=R**Q(5,2)/(1-Q(1,4)))
print('NS 192 geometric summation controls')

# Hodge: actual F=C7+ field recursion; selected CM skew fixture.
x=S.symbols('x'); f=x**3+x**2-2*x-1
red=lambda p:S.rem(S.expand(p),f,x)
a=[S.Integer(2),x]
for j in range(1,7): a.append(red(x*a[-1]-a[-2]))
need(a[7]==2 and a[6]==x)
for j in range(7): need(a[j]==a[7-j])
for i,j,k in product(range(7),repeat=3):
    scalar=red(a[i]*a[j]*a[k]);need(red(scalar-a[k]*a[j]*a[i])==0)
# 6D nondegenerate alternating form; wedge cube via all 90 ordered pair partitions.
J=S.diag(*([S.Matrix([[0,1],[-1,0]])]*3));need(J.T==-J and J.det()==1)
coeff=0; count=0
for p in permutations(range(6)):
    if not all(p[j]<p[j+1] for j in (0,2,4)):continue
    s=(-1)**sum(p[i]>p[j] for i in range(6) for j in range(i+1,6))
    coeff+=s*J[p[0],p[1]]*J[p[2],p[3]]*J[p[4],p[5]];count+=1
need(count==90 and coeff==6)
print('Hodge 343 scalar product controls, 90 ordered pair partitions, nonzero wedge cube')
