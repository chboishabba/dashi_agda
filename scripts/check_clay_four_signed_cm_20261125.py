"""Finite controls for actual source lemmas, not universal Clay proofs."""
from fractions import Fraction as Q
from itertools import product
import sympy as S

def need(ok):
    if not ok: raise ArithmeticError('regression failed')

# RH: analytic min bound checked at exact rational arguments; constant by xi.
for k in range(401):
    y=Q(k,10)
    m=1 if y<=4 else 4/y
    need(m*(y+Q(1,4))<=Q(17,4))
print('RH 401 envelope controls; xi mass bound factor 17/4')

# BSD E32, psi_3=3x^4-6x^2-1. No integral roots mod 8 or mod 3.
x=S.symbols('x'); psi=3*x**4-6*x**2-1
for m in (3,8):
    need(all(int(psi.subs(x,a))%m!=0 for a in range(m)))
# Integral valuation comparisons for v(x)=-k, k>=1 (all k by linear slopes).
for k in range(1,65):
    need(-4*k<min(1-2*k,0)) # Q2 leading coefficient unit
    need(1-4*k<min(1-2*k,0)) # Q3
I=S.Matrix([[0,-1],[1,0]])
need(I*I==-S.eye(2))
G=[]; C=[]; N=[]
for v in product(range(3),repeat=4):
    A=S.Matrix(2,2,v)
    if int(A.det())%3==0:continue
    G.append(v)
    mod=lambda B:B.applyfunc(lambda y:int(y)%3)
    if mod(A*I-I*A)==S.zeros(2):C.append(v)
    if mod(A*I-I*A)==S.zeros(2) or mod(A*I+I*A)==S.zeros(2):N.append(v)
need((len(G),len(C),len(N))==(48,8,16))
print('BSD 11 local integral residues, 128 valuation controls; centralizer/normalizer 8/16')

# NS: exact signed strain and dyadic convolution kernels.
for i in range(-12,13):
    for j in range(-12,i+1):
        # high strain in high slot gives (L/R)^(1/2); square exact.
        need(Q(2)**(j-i)<=1)
        need(Q(2)**(2*(j-i))<=1)
for a,b,c in product(range(-2,3),repeat=3):
    A=S.Matrix([[a,b,c],[-b,-a,1],[-c,-1,0]])
    w=S.Matrix([a,b,c]); sym=(A+A.T)/2
    need((w.T*A*w)[0]==(w.T*sym*w)[0] and S.trace(sym)==0)
print('NS 650 dyadic weight checks, 125 signed strain identities')

# Hodge: finite nonsplit rank-six skew chart over F_13 for conductor 7.
p=13; f=x**3+x**2-2*x-1
roots=[a for a in range(p) if int(f.subs(x,a))%p==0]
need(len(roots)==3)
for a in roots:need(pow((a-2)%p,(p-1)//2,p)==p-1)
# Construct anti-invariant generator via even irreducible polynomial.
poly=None
for a,b,c in product(range(p),repeat=3):
    if c==0:continue
    h=S.Poly(x**6+a*x**4+b*x*x+c,x,modulus=p)
    if h.is_irreducible: poly=h;break
need(poly is not None)
red=lambda z:S.Poly(z,x,modulus=p).rem(poly).as_expr()
# Trace from companion multiplication matrices; involution alpha -> -alpha.
def mat(z):
    return S.Matrix(6,6,lambda i,j:int(S.Poly(red(z*x**j),x).nth(i))%p)
M=mat(x)
B=S.Matrix(6,6,lambda i,j:int(S.trace(mat((-1)**j*x**(i+j))))%p)
mod=lambda A:A.applyfunc(lambda z:int(z)%p)
need(B==B.T and int(B.det())%p!=0)
need(mod(M.T*B+B*M)==S.zeros(6))
need(pow((-int(B.det()))%p,(p-1)//2,p)==p-1)
need(S.Poly(M.charpoly(x).as_expr(),x,modulus=p)==poly)
print('Hodge theta roots',roots,'finite irreducible skew polynomial',poly.as_expr(),'Gram determinant mod13',int(B.det())%p)
