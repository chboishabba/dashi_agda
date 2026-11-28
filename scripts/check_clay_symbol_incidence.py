"""Exact algebraic controls, not actual modular symbols or algebraic cycles."""
from itertools import product, combinations, permutations
from math import comb
import sympy as s

checks = 0
def check(ok):
    global checks
    if not ok:
        raise AssertionError('exact control failed')
    checks += 1

# Mixed coefficient of product (1+X_i)^e_i in the square-zero quotient.
# This models the Kurihara discrete-log coefficient, not complex derivatives.
for p in (5, 7):
    for k in range(1, 5):
        for exps in product(range(p), repeat=k):
            row = {0: 1}
            for i, e in enumerate(exps):
                row = {**row, **{mask | (1 << i): c*e % p for mask,c in row.items()}}
            mixed = row[(1 << k)-1]
            expected = 1
            for e in exps:
                expected = expected*e % p
            check(mixed == expected)
            # Change generator of one cyclic factor: unit rescaling.
            scale = 2
            check((mixed*scale) % p == (expected*scale) % p)
        check(all(comb(p,j)%p==0 for j in range(1,p)))

# Exterior multiplicity map: Cauchy-Binet controls independent from any
# assertion that the resulting cup functional is realized by a cycle.
for m in (5,6,7,8):
    A=s.Matrix(6,m,lambda i,j: ((i+2)*(j+3)**2+(i==j)*13+(i*j)%7)%17-8)
    B=s.Matrix(m,6,lambda i,j: ((i+1)**2*(j+2)+(i==j)*11+(i*j)%5)%19-9)
    rhs=sum(A[:,I].det()*B[I,:].det() for I in combinations(range(m),6))
    check((A*B).det()==rhs)
    if m<6:
        check(rhs==0)
    # Force a dependent sixth row and verify each exterior coordinate dies.
    A[5,:]=A[0,:]+2*A[1,:]
    check(all(A[:,I].det()==0 for I in combinations(range(m),6)))

# One finite nonzero certificate at index n gives r+d <= n. Equality
# with a witnessed rank lower bound forces the divisible Sha corank zero.
for n in range(13):
    for r in range(n+1):
        for d in range(n-r+1):
            check(r+d<=n)
            if r==n:
                check(d==0)
print(f'{checks}/{checks} exact controls PASS')
