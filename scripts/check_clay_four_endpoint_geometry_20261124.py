import sympy as S
from itertools import product

# BSD: actual selected E and E' witnesses; bad-place support is proved
# in the note by valuations, not inferred from these finite checks.
assert 4**2 == 2**3 + 4*2
assert 0**2 == 0**3 - 0
for p, expected in ((3, 4), (5, 8)):
    assert 1 + sum((y*y-x*x*x+x) % p == 0 for x,y in product(range(p), repeat=2)) == expected
print('BSD: 4 exact selected arithmetic fixture checks')

# NS: original same-output projected off-diagonal cells. Use actual
# divergence-free complex Fourier modes, not arbitrary Gram annotations.
k = S.Matrix([1, 1, 0]); q2 = k.dot(k)
P = S.eye(3)-k*k.T/q2
rows = [(S.Matrix([1,0,0]), S.Matrix([0,1,0]), S.Matrix([0,1,1]), S.Matrix([1,0,1])),
        (S.Matrix([0,1,0]), S.Matrix([1,0,0]), S.Matrix([1,0,S.I]), S.Matrix([0,-1,1])),
        (S.Matrix([1,0,1]), S.Matrix([0,1,-1]), S.Matrix([1,1,-1]), S.Matrix([1,1,1]))]
count=0
for eta,zeta,v,w in rows:
    assert eta+zeta==k and eta.dot(v)==0 and zeta.dot(w)==0
    b=P*(S.I*k.dot(v)*w)
    n=lambda a:S.simplify(a.dot(a.conjugate()))
    for ee,zz,vv,ww in rows:
        c=P*(S.I*k.dot(vv)*ww)
        g=2*S.re(b.dot(c.conjugate()))
        for residual in (0,1,7):
            a=2*q2; C=S.Rational(residual,a*(a+residual))
            assert C==1/a-1/(a+residual)
            assert (C*g)**2 <= n(v)*n(w)*n(vv)*n(ww)
            count+=1
print('NS:',count,'exact same-output signed pair fixtures')

# Hodge: quotient projective bundle rank 3; h^3=c1 h^2-c2 h+c3.
# Universal Chern symbols, exact triangular coefficient extraction.
c1,c2,c3,x0,x1,x2=S.symbols('c1 c2 c3 x0 x1 x2')
M=S.Matrix([[0,0,1],[0,1,c1],[1,c1,c1*c1-c2]])
x=S.Matrix([x0,x1,x2]); y=M*x
assert M.det()==-1
assert (M.inv()*M)==S.eye(3)
a2=y[0]; a1=S.expand(y[1]-c1*a2)
a0=S.expand(y[2]-c1*a1-(c1*c1-c2)*a2)
assert S.Matrix([a0,a1,a2])==x
assert S.expand((c1*c1-c2)*c1-c1*c2+c3)==c1**3-2*c1*c2+c3
print('Hodge: 4 exact universal projective-bundle identities')
