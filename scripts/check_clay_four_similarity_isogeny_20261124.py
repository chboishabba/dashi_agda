"""Exact local regressions for four endpoint cuts; not kernel/PDE certificates."""
import sympy as S
from itertools import product

# Hodge: Varesco Proposition 2.6's actual rational quadratic-space matrices.
Q1 = S.diag(1, -1)
Q2 = S.diag(-2, -2)
A1 = S.Matrix([[S.Rational(3,2), -S.Rational(1,2)], [S.Rational(1,2), -S.Rational(3,2)]])
A2 = S.Matrix([[1,1],[1,-1]])
Q = S.diag(Q1,Q1,Q2,Q2,Q2,Q2)
A = S.diag(A1,A1,A2,A2,A2,A2)
assert A*A == 2*S.eye(12)
assert A.T*Q == Q*A
assert A.T*Q*A == 2*Q
assert A.charpoly().as_expr() == S.expand((A.charpoly().gen**2-2)**6)
assert Q.det() == 256
# Two positive and four negative directions in the +sqrt(2) eigenspace.
vs = (A-S.sqrt(2)*S.eye(12)).nullspace()
V = S.Matrix.hstack(*vs)
G = S.simplify(V.T*Q*V)
assert len(vs)==6 and G.is_diagonal()
assert sum(bool(x>0) for x in G.diagonal())==2
assert sum(bool(x<0) for x in G.diagonal())==4
print('Hodge: 8 exact source quadratic-space identities')

# BSD: prime-to-degree multiplication is reversible on the full finite tower.
count=0
for ell,m,n in product((2,3,5,7),(2,3,5,6,10,15),range(1,5)):
    if S.gcd(ell,m)!=1: continue
    mod=ell**n
    inv=pow(m,-1,mod)
    for x in (0,1,mod//2,mod-1):
        assert (inv*m*x)%mod==x
        count+=1
print('BSD:',count,'prime-to-degree inverse fixtures')

# NS: fixed energy spatial compression, physical frequency/measure indices.
lam=S.symbols('lambda', positive=True)
b=S.symbols('b', real=True)
# Fourier velocity lambda^-3/2, cell lambda^-2, Gram lambda^-4,
# saturation lambda^-2, two input measures lambda^6, output lambda^3,
# time lambda^-2, output weight lambda^-b.
assert S.simplify(lam**(-4-2+6+3-2)*lam**(-b)-lam**(1-b))==0
assert S.simplify(lam**(1-b)).subs(b,1)==1
# General split evaluated at R=sqrt(D/E) for rational weights.
E,D,R=S.symbols('E D R', positive=True)
for beta in [S.Rational(j,2) for j in range(6)]:
    lhs=(R**(3-beta)*E**2+R**(-beta)*E**S.Rational(1,2)*D**S.Rational(3,2)).subs(R,S.sqrt(D/E))
    rhs=2*E**((1+beta)/2)*D**((3-beta)/2)
    assert S.simplify(lhs-rhs)==0
print('NS: 8 exact scaling and split identities')

# RH: exact integer arithmetic observer, not a test of universal inequalities.
count=0
for n in range(1,301):
    N=S.prod(sum(p**j for j in range(a+1)) for p,a in S.factorint(n).items())
    assert N==S.divisor_sigma(n)
    assert S.Rational(N,n)==S.prod((1-S.Rational(1,p)**(a+1))/(1-S.Rational(1,p)) for p,a in S.factorint(n).items())
    count+=1
print('RH: 300 exact divisor-factorization fixtures')
