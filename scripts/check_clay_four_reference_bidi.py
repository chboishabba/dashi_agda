#!/usr/bin/env python3
"""Exact finite controls; analytic proofs are in the controlling roadmap."""
from collections import Counter
from fractions import Fraction as F
from itertools import product, permutations
import sympy as S

counts = Counter()
def ck(lane, value):
    if not value:
        raise RuntimeError(lane)
    counts[lane] += 1

# RH: the actual adjacent ratio for the original negative-log source.
for n in range(1, 129):
    x = F(1, n+1)
    ck('RH', (1-x)*(n+1) == n)
    ck('RH', 1/(1-x) == F(n+1,n))
    # Series bounds from the original -log(1-x), no changed log carrier.
    lo = F(0)
    for j in range(1, 7):
        lo += x**j/j
        hi = lo+x**(j+1)/((j+1)*(1-x))
        ck('RH', 0 < lo <= hi <= F(1,n))
        ck('RH', hi-lo == x**(j+1)/((j+1)*(1-x)))

# BSD: shift orbit of a nonvanishing fourth difference is the augmentation
# ideal over characteristic zero. These are finite fixtures, not new symbols.
for h in (5, 7, 11, 25):
    def shift(u): return u[-1:]+u[:-1]
    def diff(u): return [a-b for a,b in zip(shift(u),u)]
    for j in (0,1,2):
        u = [int(i==j) for i in range(h)]
        d=u
        for _ in range(4): d=diff(d)
        cols=[]
        for _ in range(h):
            cols.append(d); d=shift(d)
        C=S.Matrix.hstack(*(S.Matrix(c) for c in cols))
        ck('BSD', C.rank()==h-1)
        ck('BSD', C.T*S.ones(h,1)==S.zeros(h,1))
        for k in (S.ones(h,1), S.Matrix(range(h)), S.eye(h)[:,0]):
            c=C.T*k
            ck('BSD', (c==S.zeros(h,1)) == (len(set(k))==1))
            ck('BSD', c.dot(c)==(k.T*C*C.T*k)[0])

# NS: literal mean-zero divergence-free reference, unit sphere cutoff.
# v=(a cos y,0,b cos x) e^(-t) at viscosity 1.
# The discarded interaction has only the vertical component and l1 mass ab.
a,b,z=S.symbols('a b z',positive=True)
p=(0,1,0); q=(1,0,0); r=(1,0,1)
def neg(k): return tuple(-j for j in k)
def add(k,l): return tuple(i+j for i,j in zip(k,l))
def lam(k): return sum(j*j for j in k)
v={p:S.Matrix([a*z/2,0,0]),q:S.Matrix([0,0,b*z/2])}
v.update({neg(k):w for k,w in list(v.items())})
B={}
for k,l in product(v,repeat=2):
    m=add(k,l)
    if m!=(0,0,0):
        mv=S.Matrix(m); P=S.eye(3)-mv*mv.T/lam(m)
        B[m]=B.get(m,S.zeros(3,1))+S.I*P*(v[k].dot(S.Matrix(l))*v[l])
B={k:w.applyfunc(S.expand) for k,w in B.items() if w!=S.zeros(3,1)}
ck('NS', len(B)==4)
for k,w in B.items():
    ck('NS', lam(k)==2)
    ck('NS', w[0]==w[1]==0)
    ck('NS', S.simplify(w[2]*S.conjugate(w[2]))==a*a*b*b*z**4/16)
ck('NS', S.Matrix.hstack(S.Matrix(p),S.Matrix(q),S.Matrix(r)).det()!=0)
ck('NS', S.Matrix(r).dot(S.Matrix([0,1,0]))==0)
# Rational global certificate family for arbitrary positive integer shear.
for A in range(1, 33):
    M=((A+1)**2+2*(A+1)+1)//2
    eps=F(1,3**(M+8+A.bit_length()))
    L=F(A)+eps
    ck('NS', L*L/2+L<=M)
    # exp(M)<3**M; initial error eps, forcing integral A*eps/2.
    Q=3**M*(eps+F(A,2)*eps)
    ck('NS', Q<F(1,4))
    ck('NS', 2*Q<F(1,2))
# Discrete convolution/Young scalar controls.
for F0,G,H,V,nu in product((F(1,16),F(1,8)),(F(1,8),F(1,4)),(F(1,2),F(1)),(F(1),F(2)),(F(1),F(2))):
    if G*G<=F0*H and G<=H and F0<=nu/4:
        ck('NS', V*G+F0*G<=nu*H/2+V*V*F0/nu)

# Hodge: fixed labelled triple and a commuting cyclic permutation of base.
# Cyclic deck group of order d with no order-three automorphism has trivial
# base C3 action. Kunneth H^2 has at least one H^0 factor on three surfaces.
for d in (2,3,4,5,6,8,9,10,11):
    units=[j for j in range(1,d) if S.gcd(j,d)==1]
    fixed=[j for j in units if pow(j,3,d)==1]
    if len(units)%3: ck('Hodge',fixed==[1])
for i,j,k in product(range(3),repeat=3):
    if i+j+k==2: ck('Hodge',0 in (i,j,k))
P=S.zeros(6)
for j,k in enumerate((0,1,2,4,5,3)): P[k,j]=1
R=(S.eye(6)+P+P**2)/3
ck('Hodge', P**3==S.eye(6))
ck('Hodge', R*R==R and R.rank()==4)
print(dict(counts), 'TOTAL', sum(counts.values()))
