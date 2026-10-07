#!/usr/bin/env python3
from fractions import Fraction as F
from itertools import combinations, product
import runpy
import sympy as sp

# Recover the F4 root-weight spectrum directly from the exact rational Albert
# derivation decomposition.  We use the A-projection tri(O)->so(8), choose the
# four standard coordinate-plane rotations as a Cartan, solve their unique
# triality triples, and inspect one separating Cartan element with coefficients
# (2,20,200,2000).

ns=runpy.run_path('scripts/check_rational_albert_triality_derivation_decomposition.py')
TB=ns['TB']; pairs=ns['pairs']; skew_matrix=ns['skew_matrix']; conj_twist=ns['conj_twist']
rank=ns['rank']

# A-projection basis coordinates.
Aproj=[[t.get(q,F(0)) for q in range(28)] for t in TB]

def solve_columns(cols,target):
    n=len(cols); M=[[cols[j][i] for j in range(n)]+[target[i]] for i in range(n)]
    for c in range(n):
        p=next(r for r in range(c,n) if M[r][c]); M[c],M[p]=M[p],M[c]
        z=M[c][c];M[c]=[x/z for x in M[c]]
        for r in range(n):
            if r!=c and M[r][c]:
                z=M[r][c];M[r]=[M[r][j]-z*M[c][j] for j in range(n+1)]
    return [M[i][-1] for i in range(n)]

def mm8(A,B): return [[sum(A[i][k]*B[k][j] for k in range(8)) for j in range(8)] for i in range(8)]
def comm8(A,B):
    AB=mm8(A,B);BA=mm8(B,A)
    return [[AB[i][j]-BA[i][j] for j in range(8)] for i in range(8)]
def skew_coeffs(M): return [M[i][j] for i,j in pairs]

# Reconstruct all triality triple matrices.
tri=[]
for t in TB:
    tri.append((skew_matrix(t,0),skew_matrix(t,28),skew_matrix(t,56)))

cartan_pairs=[(0,1),(2,3),(4,5),(6,7)]
cartan=[]
for pair in cartan_pairs:
    q=pairs.index(pair); target=[F(0)]*28;target[q]=F(1)
    cs=solve_columns(Aproj,target)
    triple=[]
    for block in range(3):
        M=[[F(0)]*8 for _ in range(8)]
        for c,T in zip(cs,tri):
            for i in range(8):
                for j in range(8): M[i][j]+=c*T[block][i][j]
        triple.append(M)
    cartan.append(tuple(triple))

# All four components commute in each of the three triality roles.
for role in range(3):
    for i,j in combinations(range(4),2):
        assert not any(any(x for x in row) for row in comm8(cartan[i][role],cartan[j][role]))

sep=[2,20,200,2000]
I=sp.I

def eigvals8(role):
    M=sp.Matrix([[sum(sp.Rational(sep[h])*sp.Rational(cartan[h][role][i][j].numerator,cartan[h][role][i][j].denominator)
                      for h in range(4)) for j in range(8)] for i in range(8)])
    return M.eigenvals()

# Triality adjoint action is computed through the faithful A projection.
HA=[[F(0)]*8 for _ in range(8)]
for c,T in zip(sep,cartan):
    for i in range(8):
        for j in range(8): HA[i][j]+=F(c)*T[0][i][j]

def solve_A(target): return solve_columns(Aproj,target)
cols=[]
for A,B,C in tri:
    cols.append(solve_A(skew_coeffs(comm8(HA,A))))
Adj=sp.Matrix([[sp.Rational(cols[j][i].numerator,cols[j][i].denominator) for j in range(28)] for i in range(28)])
adj=Adj.eigenvals()

# Expected D4 adjoint roots: four zero Cartan directions + ±ci±cj.
expected_long=[0]*4
for i,j in combinations(range(4),2):
    for si,sj in product((-1,1),repeat=2): expected_long.append(si*sep[i]+sj*sep[j])
actual_long=[]
for ev,m in adj.items():
    assert sp.simplify(ev/I).is_Rational
    actual_long += [int(sp.simplify(ev/I))]*m
assert sorted(actual_long)==sorted(expected_long)

# Vector weights ±ci.
expected_v=sorted([s*c for c in sep for s in (-1,1)])
# Spinor half-weights, separated by parity of minus signs.
spin_even=[];spin_odd=[]
for signs in product((-1,1),repeat=4):
    val=sum(s*c for s,c in zip(signs,sep))//2
    (spin_even if sum(s<0 for s in signs)%2==0 else spin_odd).append(val)

def imag_spectrum(role):
    out=[]
    for ev,m in eigvals8(role).items(): out += [int(sp.simplify(ev/I))]*m
    return sorted(out)

specA=imag_spectrum(0); specB=imag_spectrum(1); specC=imag_spectrum(2)
assert specA==expected_v
# Under this repository convention B is odd spinor and C even spinor.
assert specB==sorted(spin_odd)
assert specC==sorted(spin_even)

# 4 zero + 48 nonzero root spaces.
assert actual_long.count(0)==4
assert (len(actual_long)-4)+len(specA)+len(specB)+len(specC)==48

print('Cartan dimension:',actual_long.count(0))
print('D4 long-root weights:',sorted(x for x in actual_long if x))
print('8v weights:',specA)
print('8s(odd) weights:',specB)
print('8c(even) weights:',specC)
print('root spaces:',48,'derivation dimension:',52)
print('PASS: exact Albert derivation spectrum is the F4 root multiset')
