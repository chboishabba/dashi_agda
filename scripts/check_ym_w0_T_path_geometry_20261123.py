#!/usr/bin/env python3
"""Exact path-disintegration correction to false independent scalarized T masses.
A finite positive operator example ONLY; not a CMP119 physical Haar weld.
"""
import sympy as S
s,t=S.symbols('s t')
A=S.Matrix([[2,1],[1,3]]); B=S.Matrix([[3,2],[1,2]])
F=S.diag(0,2);G=S.diag(2,0)
l=S.Matrix([[1,0]]);r=S.Matrix([1,1]);I=S.eye(2)
orig=S.expand((l*A*(I+s*F)*B*(I+t*G)*r)[0])
# A path is (a,b,c); the disjoint component factors are conditional on
# the SAME path; never independently sum over b in either factor.
paths=[(a,b,c) for a in range(2) for b in range(2) for c in range(2)
       if l[0,a] != 0 and r[c] != 0]
def residual(a,b,c):return l[0,a]*r[c]
def step1(a,b,c):return A[a,b]*(1+s*F[b,b])
def step2(a,b,c):return B[b,c]*(1+t*G[c,c])
assembled=S.expand(sum(residual(*p)*step1(*p)*step2(*p) for p in paths))
assert assembled==orig==13+6*s+14*t+4*s*t
assert len(paths)==4
coeff=lambda x:tuple(S.expand(x).coeff(s,a).coeff(t,b) for a,b in [(0,0),(1,0),(0,1),(1,1)])
assert coeff(orig)==coeff(assembled)==(13,6,14,4)
# Source-style Eq2.18 sequence sum, 2.19 product of components, 2.20
# ordered step product: one component per path, two steps per component.
seqsum=S.expand(sum(residual(*p)*S.prod((step1(*p),step2(*p))) for p in paths))
assert seqsum==orig
# Exact conditional intermediate-state fibres: b slices, no normalization.
for b in range(2):
    summand=S.expand(sum(residual(*p)*step1(*p)*step2(*p) for p in paths if p[1]==b))
    print(f'b={b}: {summand}')
# A valid *disjoint-component* product is over a Cartesian-product carrier,
# and integrand separates on those coordinates. Witness direct finite Fubini.
x=(S.Rational(2),S.Rational(3)); y=(S.Rational(5),S.Rational(7))
assert sum(u*v for u in x for v in y)==sum(x)*sum(y)
# But a shared b or cross-coupled weight invalidates this factorization.
assert sum(A[0,b]*B[b,c] for b in range(2) for c in range(2)) != sum(A[0,b] for b in range(2))*sum(B[b,c] for b in range(2) for c in range(2))
print('PASS source-style path decomposition: 4 shared-state sequences, 2 ordered T steps each')
print(f'PASS full 1/F/G/FG coefficients {coeff(seqsum)} and residuals')
print('PASS genuine Cartesian/disjoint Fubini vs shared-state negative control')
print('NO assertion of CMP119 literal admissible indices, physical Wilson integration, W3 or Clay theorem')
