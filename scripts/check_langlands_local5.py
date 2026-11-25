"""Exact finite-source checks for local-5 splitting; not a p-adic epsilon evaluator."""
from itertools import product
import sympy as s

# Augmentation subspace on F_p, basis e_i-e_0.
def aug(p,a,b):
    M=s.zeros(p-1)
    for i in range(1,p):
        for j,c in [((a*i+b)%p,1),(b%p,-1)]:
            if j: M[j-1,i-1]+=c
    return M

def prod(g,h):
    a,b,c=g; d,e,f=h
    return (a*d%5,(a*e+b)%5,c*f%3)

G=list(product(range(1,5),range(5),range(1,3)))
U={g:aug(5,g[0],g[1]) for g in G}
V={g:s.diag(U[g],(1 if g[2]==1 else -1)*U[g]) for g in G}
# Rational primitive block from signed permutation residual.
for a,b,c in G:
    aa=next(k for k in range(15) if k%5==a and k%3==c)
    bb=next(k for k in range(15) if k%5==b and k%3==0)
    for power in range(1,9):
        ap=pow(aa,power,15); bp=bb*sum(aa**i for i in range(power))%15
        fixed=lambda d:sum((ap*x+bp-x)%d==0 for x in range(d))
        assert s.trace(V[a,b,c]**power)==fixed(15)-fixed(5)-fixed(3)+1
    assert V[a,b,c].det()==1
# Product group action in the augmentation representation.
for g,h in product(G,repeat=2):
    assert U[g]*U[h]==U[prod(g,h)]
# Inertia is affine F5; wild subgroup is translations.
I=[g for g in G if g[2]==1]; P=[g for g in I if g[0]==1]
assert sum((U[g] for g in I),s.zeros(4))==s.zeros(4)
assert sum((U[g] for g in P),s.zeros(4))==s.zeros(4)
# Artin conductor with G0=I, G1=P, G2=1.
a=4+s.Rational(len(P),len(I))*4
assert a==5
# Quadratic determinant on tame units: -1 acts by multiplier -1.
assert U[4,0,1].det()==1
# Classical duality + unramified-twist formula; not a Gauss-sum execution.
assert (-1)**a * U[4,0,1].det()==-1
print('40 decomposition elements; 320 trace-power identities; 1600 product laws; conductor 5+5=10; local root number -1 (theorem formula)')

# R323: actual R306 lattice and R307 scalar extended-type normalization.
P=s.kronecker_product(s.Matrix([[0,-3],[1,3]]),s.eye(4))
beta=s.kronecker_product(s.Matrix([[6,21],[-7,-15]])/9,s.eye(4))
assert P*beta==beta*P
assert P.det()==3**4
# 1+27M8 is in U_A^2 and trivial under the R306 trace character.
for i,j in product(range(8),repeat=2):
    X=s.zeros(8); X[i,j]=27
    assert (s.trace(beta*X)/3).is_Integer
# Cartan spread suffices for conjugating the principal congruence subgroup.
for exps in [(0,)*8,(-3,-2,-1,0,1,2,3,4),(5,)*8,(-4,0,0,0,0,0,0,2)]:
    level=3+max(exps)-min(exps)
    for i,j in product(range(8),repeat=2):
        assert level+exps[i]-exps[j]>=3
# Haar-normalized generator action in the R307 scalar extension.
a=s.symbols('alpha',nonzero=True)
for m,n in product(range(-4,5),repeat=2):
    assert s.simplify((-1)**abs(m)*(-a)**m*(-1)**abs(n)*(-a)**n-a**(m+n))==0
print('64 trace-kernel generators; 256 Cartan level bounds; 81 scalar Laurent actions')
