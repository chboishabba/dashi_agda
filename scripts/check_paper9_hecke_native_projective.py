"""Independent exact reference for the native Hecke chart weld.

This replays integer/rational algebra only, not Agda elaboration.
"""
from math import prod
import sympy as s

P = 41
I = (1, 0, 0, 1)
S = (0, -1, 1, 0)
T = (1, 1, 0, 1)


def mul(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h


def chart(i):
    return (1, i, 0, P) if i < P else (P, 0, 0, 1)


def correction(i, j, g):
    a, b, c, d = chart(j)
    x = mul(mul(chart(i), g), (d, -b, -c, a))
    assert all(v % P == 0 for v in x)
    return tuple(v//P for v in x)


def tp(q):
    return ('t',)*q if q >= 0 else ('s','s','s','t','s','t','s')*(-q)


def word(m):
    a,b,c,d = m
    if c == 0:
        assert a == d and abs(a) == 1
        return tp(b) if a == 1 else ('s','s')+tp(-b)
    q = a//c
    return tp(q)+('s','s','s')+word(mul(S,mul((1,-q,0,1),m)))


def matrix(w):
    m = I
    for g in w:
        m = mul(m, S if g == 's' else T)
    return m


si = [P]+[(-pow(i,-1,P)) % P for i in range(1,P)]+[0]
ti = [(i+1)%P for i in range(P)]+[P]
checks = 0
for g, ix in ((S,si),(T,ti)):
    assert sorted(ix) == list(range(P+1))
    for i,j in enumerate(ix):
        c = correction(i,j,g)
        assert c[0]*c[3]-c[1]*c[2] == 1
        assert mul(chart(i),g) == mul(c,chart(j))
        assert matrix(word(c)) == c
        checks += 3
    factors = [2*i-31 for i in range(P+1)]
    assert prod(factors) == prod(factors[j] for j in ix)
print('integer correction determinant, edge, and word checks', checks)

# Homogeneous composition and cancellation use the same scalar twice.
a,b,c,d,u,v,f,z = s.symbols('a b c d u v f z')
assert s.expand(a*(f*z)+b*f-f*(a*z+b)) == 0
assert s.expand(c*(f*z)+d*f-f*(c*z+d)) == 0
w,e4,e6 = s.symbols('w e4 e6')
assert s.expand((w**4*e4)**3-w**12*e4**3) == 0
assert s.expand(((w**4*e4)**3-(w**6*e6)**2)-w**12*(e4**3-e6**2)) == 0
N,D,j,N1,D1 = s.symbols('N D j N1 D1')
assert s.expand((N*D1-D*N1).subs({N:D*j,N1:D1*j})) == 0
print('homogeneous composition, weight and fixed-factor checks', 5)

# CM parameter lives in the exact quadratic field, not a numeric root.
tau=(-1+s.I*s.sqrt(163))/2
assert s.simplify(tau*tau+tau+41) == 0
assert s.simplify(tau*(tau+1)/41+1) == 0
assert s.simplify((tau+1)*tau/41+1) == 0
assert s.simplify((tau+1)/41+1/tau) == 0
assert s.simplify(tau/41+1/(tau+1)) == 0
print('CM quadratic and two fixed chart checks',5)
