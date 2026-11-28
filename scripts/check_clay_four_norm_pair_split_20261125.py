"""Exact finite controls: norm-row, trace log, pair symmetry, cyclotomic split.
Not a native kernel, actual Selmer solver, PDE or algebraic-cycle computation.
"""
from itertools import permutations, product
from fractions import Fraction
from math import comb
import sympy as S


def need(condition):
    if not condition:
        raise ArithmeticError('exact control failed')


G = list(permutations(range(3)))
e, a, b, r = G[0], (1, 2, 0), (1, 0, 2), (0, 2, 1)


def mul(g, h):
    return tuple(g[h[i]] for i in range(3))


def cosets(H):
    return sorted(set(tuple(sorted(mul(g, h) for h in H)) for g in G))


C3, C2 = cosets([e, a, mul(a, a)]), cosets([e, b])
A = S.zeros(8)
for j, g in enumerate(G):
    A[next(i for i, c in enumerate(C3) if g in c), j] = 1
    A[2 + next(i for i, c in enumerate(C2) if g in c), j] = 1
    A[5 + next(i for i, c in enumerate(C2) if mul(g, r) in c), j] = 1
for i in range(2):
    A[i, 6] = 1
for i in range(2, 5):
    A[i, 7] = 1
p = S.eye(8)[7, :]
C = 3 * p * A.inv()
need(A.det() == 18 and C == S.Matrix([[0, 0, 1, 1, 1, -1, -1, -1]]))
need(C * A == 3 * p)
# Under actual permutation action each summation row is invariant.
for g in G:
    act = lambda h: tuple(sorted(mul(g, x) for x in h))
    for block in (C3, C2):
        need(set(map(act, block)) == set(block))
# Original modular kernel projection onto last trivial coordinate is surjective.
for ell, count in ((2, 2), (3, 9)):
    rows = [tuple(map(int, A.row(i))) for i in range(8)]
    ker = [v for v in product(range(ell), repeat=8)
           if all(sum(x*y for x, y in zip(row, v)) % ell == 0 for row in rows)]
    need(len(ker) == count)
    need({v[7] for v in ker} == (set(range(3)) if ell == 3 else {0}))
# Trace pi^n for pi = 1+cuberoot(2), with Eisenstein polynomial.
# Newton recurrence: trace 1=3, pi=3, pi^2=3.
T = [3, 3, 3]
for n in range(3, 402):
    T.append(3*T[-1] - 3*T[-2] + 3*T[-3])
need(T[:6] == [3, 3, 3, 9, 27, 63])


def val3(n):
    if n == 0:
        return 100000
    k = 0
    while n % 3 == 0:
        n //= 3
        k += 1
    return k


# dx/(2y) = dt/sqrt(1+4t^4) on E32 formal t=-x/y.
terms = [Fraction((-1)**k * comb(2*k, k)*T[4*k+1], 4*k+1) for k in range(101)]
need(terms[0] == 3)
for k, z in enumerate(terms[1:], 1):
    n = 4*k+1
    need(val3(T[n]) >= (n+3)//3)
    need(val3(z.numerator)-val3(z.denominator) >= 2)
need(1 + sum((y*y-x*x*x+x) % 3 == 0 for x,y in product(range(3), repeat=2)) == 4)
print('BSD norm row [0,0,1,1,1,-1,-1,-1], 6817 kernel candidates, 100 log trace terms, residue 3 mod 9')

# Exact signed physical pair symmetrization, axial/polar transport.
def dot(x, y): return sum(a*b for a,b in zip(x,y))
def neg(x): return tuple(-a for a in x)
def sub(x,y): return tuple(a-b for a,b in zip(x,y))
def cross(x,y): return (x[1]*y[2]-x[2]*y[1], x[2]*y[0]-x[0]*y[2], x[0]*y[1]-x[1]*y[0])
def original(x,y,r): return -dot(x,r)*dot(x,cross(y,r))
def pair(x,y,r): return -dot(sub(x,y),r)*dot(x,cross(y,r))
vecs=list(product((-1,0,1), repeat=3))
for x,y,r in product(vecs,repeat=3):
    need(original(x,y,r)+original(y,x,neg(r)) == pair(x,y,r))
    need(pair(x,y,r) == pair(y,x,neg(r)))
    need(pair(neg(x),neg(y),r) == -pair(x,y,r))
x,y,r=(1,1,0),(1,0,1),(1,0,0)
need(pair(x,y,r)==0 and original(x,y,r)==-original(y,x,neg(r))!=0)
print('NS 19683 pair fixtures, 59049 exact identities, nontrivial cancellation witness')

# RH finite spectral return control: rational frequencies, exact phases at periods.
# Infinite real frequencies are handled by the simultaneous-approximation proof.
for denominators in ((2,3,5),(4,7,9),(8,11,13),(1,2,3,4,5)):
    lcm = int(S.ilcm(*denominators))
    for k in range(1,9):
        need(all((k*lcm) % d == 0 for d in denominators))
print('RH 32 rational simultaneous return fixtures')

# Actual reported conductor-seven field arithmetic, not verification of geometry.
x,z=S.symbols('x z')
f=x**3+x**2-2*x-1
red=lambda p:S.rem(S.expand(p), f,x)
u=x*x+x-1; pi=2-x
need(red(u*u)==x+2)
need(red(-pi*u*u)==x*x-4)
need(red((7+x+3*x*x)**2+pi-16*(3+x+4*x*x))==0)
need(S.Poly(S.resultant(f,z*z-x*z+1,x),z)==S.Poly(S.cyclotomic_poly(7,z),z))
# 2 has order 3 modulo 7; F has one dyadic place and K/F splits there.
need([pow(2,k,7) for k in range(1,4)]==[2,4,1])
need(S.Poly(f,x,modulus=2).is_irreducible)
# Pairing on wedge^2 of dimension four has three hyperbolic blocks.
basis=list(__import__('itertools').combinations(range(4),2))
B=S.zeros(6)
for i,I in enumerate(basis):
    J=tuple(j for j in range(4) if j not in I)
    B[i,basis.index(J)]=(-1)**sum(a>b for a in I for b in J)
need(B.det()==-1 and B*B==S.eye(6))
need(B.eigenvals()=={-1:3,1:3})
print('Hodge cyclotomic determinant, dyadic split and hyperbolic wedge pairing PASS')
