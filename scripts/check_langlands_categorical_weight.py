"""R376-380: arithmetic witnesses for cited categorical theorems, not a sheaf backend."""
from itertools import combinations, product
from math import gcd, comb
from fractions import Fraction
import sympy as s

labels = (1,2,4,7,8,11,13,14)
alpha = s.Symbol('alpha', nonzero=True)
z = s.Symbol('z', nonzero=True)
sector = {j:i for i,j in enumerate((1,3,4,2))}
perm = [labels.index(13*j%15) for j in labels]
invol = [labels.index(11*j%15) for j in labels]
exp = [int(sector[j%5]==3) for j in labels]
F = s.zeros(8)
A = s.zeros(8)
for i in range(8):
    F[perm[i],i] = alpha**exp[i]
    A[invol[i],i] = 1
assert F**4 == alpha*s.eye(8) and F.det() == alpha**2
assert A**2 == s.eye(8) and A*F == F*A
# Every translation character is distinct; centralizer diagonal and A,F transitive.
assert len(set(labels))==8
orbit={0}
while True:
    next_orbit=orbit|{perm[i] for i in orbit}|{invol[i] for i in orbit}
    if next_orbit==orbit:break
    orbit=next_orbit
assert len(orbit)==8
# Pairing signs and wrap powers on the complete exterior carrier.
def sign(seq):
    return (-1)**sum(a>b for i,a in enumerate(seq) for b in seq[i+1:])
def wedge_image(I,p,e):
    seq=[p[i] for i in I]
    return tuple(sorted(seq)),sign(seq),sum(e[i] for i in I)
all_idx=set(range(8)); checks=0; dims=[]
for k in range(9):
    inv_count=0
    for I in combinations(range(8),k):
        J=tuple(sorted(all_idx-set(I)))
        assert sign(I+J)==(-1)**(k*(8-k))*sign(J+I)
        for p,e in ((perm,exp),(invol,[0]*8)):
            Ii,a,u=wedge_image(I,p,e); Jj,b,v=wedge_image(J,p,e)
            assert a*b*sign(Ii+Jj)==sign(I+J)*sign(p)
            assert u+v==sum(e)
            assert set(Ii).isdisjoint(Jj) and set(Ii+Jj)==all_idx
            checks+=1
        assert sum(labels[i] for i in I)+sum(labels[j] for j in J)==60
        # Fixed-translation and signed reflection trace projector.
        if sum(labels[i] for i in I)%15==0:
            Ii,a,_=wedge_image(I,invol,[0]*8)
            inv_count+=1+ (a if Ii==I else 0)
    assert inv_count%2==0
    dims.append(inv_count//2)
assert dims==[1,0,2,0,5,0,2,0,1]
# Basic isocrystal representatives.  Use sigma-linear shift over Q3^nr;
# rational matrix coefficients are sigma-fixed. Positive valuation convention.
rows=[]
for d in range(-8,17):
    g=gcd(8,d); m=8//g; a=d//g
    C=s.zeros(m)
    for i in range(m): C[(i+1)%m,i]=s.Rational(3)**a if i==m-1 else 1
    Bd=s.diag(*([C]*g))
    assert Bd**m==s.Rational(3)**a*s.eye(8)
    assert abs(Bd.det())==s.Rational(3)**d
    assert gcd(abs(a),m)==1 and g*g*m*m==64
    # Whole degree retained: shifting by eight is a line-bundle twist.
    # C(a+m) is conjugate to 3*C(a) via diag(3^-i).
    Cp=C.copy();Cp[0,m-1]*=3**m
    G=s.diag(*[s.Rational(3)**(-i) for i in range(m)])
    assert G*(3*C)*G.inv()==Cp
    if 0<=d<8:rows.append((d,g,m,a))
# Exact LS-type guard for this original fixed-inertia unramified-twist family.
# Fourth Frobenius power gives loop scalar; Tate twist convention +/- is symmetric.
def ls(alphas):
    return all(x!=y and x!=81*y and 81*x!=y
               for i,x in enumerate(alphas) for y in alphas[i+1:])
assert ls([Fraction(1)]) and ls([Fraction(1),Fraction(2),Fraction(5)])
assert not ls([Fraction(1),Fraction(1)])
for n in range(2,9):
    assert not ls([Fraction(81)**i for i in range(n)])
# Degree-shift line equivalences are invertible; Hecke of wedge^k is not
# an equivalence for 0<k<8, since its coefficient rank is >1.
for k in range(9):
    assert comb(8,k)==comb(8,8-k)
    assert (comb(8,k)==1)==(k in (0,8))
print('exterior equivariant complement checks:',checks,'inertia-fixed dimensions:',dims)
print('basic residue classes (degree, matrix rank, division degree, numerator):',rows)
print('25 basic isocrystal and determinant-twist checks; 10 LS examples; PASS')
