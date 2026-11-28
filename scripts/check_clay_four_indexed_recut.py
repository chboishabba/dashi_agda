#!/usr/bin/env python3
from itertools import product, permutations, combinations
from collections import Counter
from math import comb
import sympy as S
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ

counts = Counter()
def ck(group, condition):
    if not condition:
        raise RuntimeError(group)
    counts[group] += 1

# RH: direct coefficient extraction from the original three-term residual.
z,a,L,h,x=S.symbols('z a L h x')
for n in range(1,8):
    E=lambda b: sum(b**j*z**j/S.factorial(j) for j in range(n+1))
    direct=(a-z)*0 # initialize symbolic expression
    # n^(1-s0) factored out; A=exp(a*h) is retained as a symbol.
    A=S.Symbol('A')
    direct=(z-a)*x*E(-L)+A*E(-L-h)-E(-L)
    for k in range(n+1):
        c=(-a*x-1)*(-L)**k/S.factorial(k)+A*(-L-h)**k/S.factorial(k)
        if k: c+=x*(-L)**(k-1)/S.factorial(k-1)
        ck('RH', S.expand(direct).coeff(z,k)==S.expand(c))

# BSD: Smith form and moment congruences of the exact fourth-difference image.
for p in (5,7,11):
    for j in range(1,5):
        h0=p**j
        B=S.Matrix([[h0,0,0],[comb(h0,2),h0,0],[comb(h0,3),comb(h0,2),h0]])
        ck('BSD', smith_normal_form(B,domain=ZZ)==h0*S.eye(3))
        ck('BSD', (B/h0).det()==1)
        ck('BSD', all(x.is_Integer for x in (B/h0).inv()))
    for j in (1,2):
        h0=p**j
        # Test fourth differences of individual cyclic basis vectors.
        for i in range(h0):
            d=[0]*h0
            for l in range(5): d[(i+l)%h0]+=(-1)**(4-l)*comb(4,l)
            ck('BSD', sum(d)==0)
            for r in (1,2,3):
                ck('BSD', sum(comb(k,r)*d[k] for k in range(h0))%h0==0)
        # Exact reduction of binomial moment addresses across a refinement.
        for i in range(p*h0):
            for r in (1,2,3):
                ck('BSD', (comb(i,r)-comb(i%h0,r))%h0==0)

# Independent chart and time transport, including noncommuting time steps.
C=[S.eye(2),S.Matrix([[0,-1],[1,0]]),S.Matrix([[1,1],[0,1]])]
U=[S.Matrix([[2,1],[0,1]]),S.Matrix([[1,0],[3,2]])]
for i,j,k in product(range(3),repeat=3):
    a0=C[j]*U[0]*C[i].inv(); a1=C[k]*U[1]*C[j].inv()
    ck('transport',a1*a0==C[k]*U[1]*U[0]*C[i].inv())
ck('transport',U[0]*U[1]!=U[1]*U[0])

# NS: exact nonvanishing of the projected stress symbol on two spectral packets.
p=S.Matrix([1,2,0]); q=S.Matrix([0,2,0]); a=S.Matrix([2,-1,0]); b=S.Matrix([1,0,0]); e2=S.Matrix([0,1,0])
P=lambda k:S.eye(3)-k*k.T/k.dot(k)
for d1,d2 in product(product((-1,0,1),repeat=3),repeat=2):
    xi=p+S.Matrix(d1)/100; eta=-q+S.Matrix(d2)/100; k=xi+eta
    u=P(xi)*a; v=P(eta)*b
    sym=-u.dot(v)*(xi*eta.T+eta*xi.T)
    ck('NS',u.dot(xi)==0 and v.dot(eta)==0)
    ck('NS',e2.dot(P(k)*sym*k)>0)
    ck('NS',k.dot(k)<min(xi.dot(xi),eta.dot(eta)))

# Hodge: fixing three coordinates, the C3-invariant part has dimension four.
even=[p for p in permutations(range(6)) if sum(p[i]>p[j] for i in range(6) for j in range(i+1,6))%2==0]
for triple in combinations(range(6),3):
    G=[p for p in even if all(p[i]==i for i in triple)]
    ck('Hodge',len(G)==3)
    M=sum((S.eye(6)[:,list(p)] for p in G),S.zeros(6))/3
    ck('Hodge',M*M==M)
    ck('Hodge',M.rank()==4)
print(dict(counts),'TOTAL',sum(counts.values()))
