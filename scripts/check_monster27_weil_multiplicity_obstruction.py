from itertools import combinations_with_replacement
from collections import Counter
from math import comb
import sympy as s


def require(ok):
    if not ok:
        raise AssertionError('C27 multiplicity obstruction')


# Conditional: canonical honest Weil factor W has W^9=I,
# its traces on powers 1..8 are nonzero, and D^9=t I.
# Actual source rank table: each of nine roots of t has rank 7290.
require(9*7290 == 729*90)
# Normalized D then has ten copies of each of nine roots of t.
# Write t=alpha^9, omega=alpha^3, alpha primitive 27th root.
# Determinant exponents mod 27; full D determinant is t, not 1.
require(sum(10*(1+3*j) for j in range(9))%27 == 9)
require(90%3 == 0)
# D=A+dual Sym^2 A, with actual A^9=t I, common phase gauge.
# Symmetric-pair weights have exponent -1-j-k in omega coordinates.
solutions=[]
checked=0
for xs in combinations_with_replacement(range(9),12):
    a=[0]*9
    for j in xs:
        a[j]+=1
    b=a.copy()
    for i in range(9):
        b[(-1-2*i)%9]+=a[i]*(a[i]+1)//2
        for j in range(i+1,9):
            b[(-1-i-j)%9]+=a[i]*a[j]
    checked+=1
    if b==[10]*9:
        solutions.append(tuple(a))
require(checked==comb(20,8)==125970)
require(len(solutions)==18)
det=Counter((12+3*sum(j*n for j,n in enumerate(a)))%27 for a in solutions)
require(det=={6:6,15:6,24:6})
require(all((-12*d)%27==9 for d in det))
# Root-coordinate change only; not a new scalar gauge of W or D.
for a in solutions:
    for r in range(9):
        ap=[a[(j+r)%9] for j in range(9)]
        b=ap.copy()
        for i in range(9):
            b[(-1-3*r-2*i)%9]+=ap[i]*(ap[i]+1)//2
            for j in range(i+1,9):
                b[(-1-3*r-i-j)%9]+=ap[i]*ap[j]
        require(b==[10]*9)
        require(sum((1+3*r+3*j)*ap[j] for j in range(9))%27 == sum((1+3*j)*a[j] for j in range(9))%27)
# General determinant identity for A + dual Sym^2 A.
x=s.symbols('x:12',nonzero=True)
require(s.cancel(s.prod(x)*s.prod(1/(x[i]*x[j]) for i in range(12) for j in range(i,12))-s.prod(x)**(-12))==0)
print('PASS 125970 spectra; 18 uniform candidates; zero determinant-one candidates; 162 root-coordinate controls; symbolic determinant law')
