"""Exact finite checks for selected E32 bounds, periodic Beltrami and Clifford bivectors.
No kernel, PDE evolution, general Selmer or Chow computation.
"""
from fractions import Fraction as Q
from math import factorial
from itertools import permutations, product
import sympy as S


def require(ok):
    if not ok:
        raise ArithmeticError('exact check failed')


# Actual E32 reduction and rational analytic bounds.
for p, expected in ((3,4),(5,8)):
    n=1+sum((y*y-x*x*x+x)%p==0 for x,y in product(range(p),repeat=2))
    require(n==expected)
# pi>3.14 and sqrt(2)<1.415 imply pi/(2 sqrt(2))>1.1.
require(Q(283,200)**2>2 and Q(157,50)/(2*Q(283,200))>Q(11,10))
require(sum(Q(11,10)**k/factorial(k) for k in range(6))>3)
q=Q(1,3)
require(1-2*q**4/(1-q)>0)
upper=2*q+4*q**5/(1-q)
require(upper==Q(56,81) and 8*upper/4<2)
print('E32: reductions 4,8; L upper',upper,'Sha upper',8*upper/4)

# Actual periodic ABC eigenfield; arbitrary real amplitudes.
x,y,z=S.symbols('x y z',real=True)
a,b,c=S.symbols('a b c',real=True)
xyz=(x,y,z)
U=S.Matrix([a*S.sin(z)+c*S.cos(y),b*S.sin(x)+a*S.cos(z),c*S.sin(y)+b*S.cos(x)])
def curl(v):return S.Matrix([S.diff(v[2],y)-S.diff(v[1],z),S.diff(v[0],z)-S.diff(v[2],x),S.diff(v[1],x)-S.diff(v[0],y)])
def simp(v):return v.applyfunc(S.trigsimp)
require(S.expand(sum(S.diff(U[i],xyz[i]) for i in range(3)))==0)
require(simp(curl(U)-U)==S.zeros(3,1))
require(simp(sum((U.diff(q,2) for q in xyz),S.zeros(3,1))+U)==S.zeros(3,1))
require(simp(U.jacobian(xyz)*U-S.Matrix([S.diff(U.dot(U)/2,q) for q in xyz]))==S.zeros(3,1))
# Full signed cube action transports curl eigenvalue with determinant.
checks=0
for p,s in product(permutations(range(3)),product((-1,1),repeat=3)):
    R=S.zeros(3)
    for i in range(3):R[i,p[i]]=s[i]
    v=R*U.subs(dict(zip(xyz,R.T*S.Matrix(xyz))),simultaneous=True)
    require(simp(curl(v)-R.det()*v)==S.zeros(3,1))
    checks+=1
print('NS: ABC symbolic stationary Euler/heat identities;',checks,'signed reflection curl transports')

# Clifford q=I_8, not a claim about the actual K3 Gram.
# e_i^2=1, even carrier 128. Omega=e_0...e_5, Omega^2=-1.
def mul(a,b):
    s=1
    for i in range(8):
        if a>>i&1 and (b&((1<<i)-1)).bit_count()%2:s=-s
    return s,a^b
basis=[m for m in range(256) if m.bit_count()%2==0]
omega=63
require(mul(omega,omega)==(-1,0))
# Nonzero vector times fixed right odd factor swaps chirality: exact signed monomial identity.
for m in basis:
    s,n=mul(1,m); t,n=mul(n,64);s*=t
    p,u=mul(omega,n)
    v,k=mul(omega,m);w,k=mul(1,k);j,k=mul(k,64)
    require(u==k and s*p==-v*w*j)
# For distinct orthogonal basis slots B(e_i,e_j)=e_i e_j.
# The inserted trace is 6! times dimension. Check all permutations.
alt=0
for perm in permutations(range(6)):
    parity=(-1)**sum(perm[i]>perm[j] for i in range(6) for j in range(i+1,6))
    sign,word=1,0
    for i in perm:
        t,word=mul(word,1<<i);sign*=t
    require(word==omega and sign==parity)
    tr=0
    for m in basis:
        t,n=mul(word,m);u,n=mul(omega,n)
        require(n==m)
        tr-=sign*t*u
    require(tr==parity*len(basis))
    alt+=parity*tr
require(alt==92160)
# P±=(I±Omega/i)/2 over Q(i); trace equal since L_Omega has no fixed basis vector.
require(all(mul(omega,m)[1]!=m for m in basis))
print('Hodge: 128 chirality swaps; 720 bivector ordered traces; inserted',alt,'two projector ranks',len(basis)//2)
