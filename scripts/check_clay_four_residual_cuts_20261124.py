import sympy as S
from itertools import product

# BSD: paired finite primary layers, abstract models, not computed curves.
count = 0
for r, d, m1, m2, m3, n in product(range(3), range(3), range(2), range(2), range(2), range(1, 7)):
    z = n*d + 2*sum(m*min(n,j) for j,m in enumerate((m1,m2,m3),1))
    zp = (n+1)*d + 2*sum(m*min(n+1,j) for j,m in enumerate((m1,m2,m3),1))
    z1 = d + 2*(m1+m2+m3)
    assert (n*r+z-n*(r+d)) % 2 == 0
    assert z1-(zp-z) == 2*sum(m for j,m in enumerate((m1,m2,m3),1) if j<=n)
    count += 1
print('BSD paired tower models:', count)

# RH: relative sixth-order remainder coefficient on the actual strip.
for j in range(-12,13):
    x = S.Rational(j,24)
    assert x**6 <= x**4/4
print('RH strip moment controls: 25')

# NS: weighted pair split at the intrinsic balancing scale.
E,D,R = S.symbols('E D R', positive=True)
assert S.simplify((R**2*E**2+E**S.Rational(1,2)*D**S.Rational(3,2)/R).subs(R,S.sqrt(D/E))-2*E*D)==0
# Abstract concentration: small bad-time measure does not control weighted mass.
for n in range(1,33):
    length = S.Rational(1,n*n)
    assert length*n*n == 1
    assert length <= S.Rational(1,n)
print('NS: 1 split identity, 32 concentration fixtures')

# Hodge: abstract real quadratic multiplication with symmetric adjoint.
A=S.Matrix([[0,2],[1,0]])
Q=S.diag(1,2)
assert A.T*Q==Q*A
assert A.T*Q*A==2*Q
assert A*A==2*S.eye(2)
a,b=S.symbols('a b', real=True)
assert S.expand((a*S.eye(2)+b*A)**2)==(a*a+2*b*b)*S.eye(2)+2*a*b*A
# CM Cayley inverse in Q(i), illustrative field identity.
t=S.symbols('t', real=True)
u=(1+S.I*t)/(1-S.I*t)
assert S.simplify(u*S.conjugate(u)-1)==0
assert S.simplify((u-1)/(u+1)-S.I*t)==0
print('Hodge: 6 field identities (not geometric cycle witnesses)')
