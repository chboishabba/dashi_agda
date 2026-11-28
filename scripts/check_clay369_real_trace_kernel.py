"""Exact reference controls for native real trace and rich-carrier source welds."""
from fractions import Fraction as Q
from itertools import product
import random
import sympy as s

if not __debug__:
    raise SystemExit('refuse optimized Python')

rng = random.Random(36920261128)
counts = {}

def check(name, good):
    if not good:
        raise AssertionError(name)
    counts[name] = counts.get(name, 0) + 1

def dot(a, b):
    return sum(x*y for x, y in zip(a, b))

def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])

def vec():
    return tuple(Q(rng.randint(-5, 5), rng.randint(1, 4)) for _ in range(3))

def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))

# Literal complex vector represented by two exact real coordinate triples.
def projection(x, v):
    a = dot(x, x)
    return tuple(z-y*dot(x, v)/a for y, z in zip(x, v))

def cell(x, u, v):
    dr, di = dot(x, u[0]), dot(x, u[1])
    vr, vi = v
    # i*(dr+i*di)*(vr+i*vi), with actual signs
    re = tuple(-dr*b-di*a for a, b in zip(vr, vi))
    im = tuple(dr*a-di*b for a, b in zip(vr, vi))
    return projection(x, re), projection(x, im)

def pm(u):
    return dot(u[0], u[0])+dot(u[1], u[1])

for _ in range(256):
    xi = vec()
    if not dot(xi, xi):
        xi = (Q(1), Q(0), Q(0))
    eta, etb = vec(), vec()
    za, zb = sub(xi, eta), sub(xi, etb)
    frequencies = (eta, za, etb, zb)
    U = {k: (cross(k, vec()), cross(k, vec())) for k in dict.fromkeys(frequencies)}
    A, B = cell(xi, U[eta], U[za]), cell(xi, U[etb], U[zb])
    G = 2*(dot(A[0], B[0])+dot(A[1], B[1]))
    nu = Q(rng.randint(1, 9), rng.randint(1, 9))
    a = nu*dot(xi, xi)
    ra, rb = (nu*(dot(k, k)+dot(z, z)) for k, z in ((eta, za), (etb, zb)))
    xa, xb = sub(eta, tuple(z/2 for z in xi)), sub(etb, tuple(z/2 for z in xi))
    residual = 2*nu*(dot(xa, xa)+dot(xb, xb))
    check('double_rate', ra+rb == a+residual and residual >= 0)
    check('projected_transverse', all(dot(xi, w)==0 for w in (*A, *B)))
    coeff = residual/(a*(a+residual))
    check('signed_kernel', G/(ra+rb)==G/a-coeff*G and 0<=coeff<=1/a)
    for k,z in ((eta,za),(etb,zb)):
        u = U[k]
        d = sum(dot(xi, w)**2 for w in u)
        check('other_input', d<=dot(z,z)*pm(u))
        check('single_rate', d<= (dot(k,k)+dot(z,z))*pm(u))

# Actual finite ordered Cauchy pair polynomial, all six phase coordinates.
t = s.symbols('t')
for size in (1, 2, 3, 4):
    for _ in range(3):
        r = [s.Rational(rng.randint(1,9),rng.randint(1,5)) for i in range(size)]
        m = [[sum(rng.randint(-3,3)*t**k for k in range(3)) for c in range(6)] for i in range(size)]
        f = [[s.diff(m[i][c],t)+r[i]*m[i][c] for c in range(6)] for i in range(size)]
        pairs = list(product(range(size),range(size),range(6)))
        C = s.expand(sum(2*m[i][c]*m[j][c]/(r[i]+r[j]) for i,j,c in pairs))
        H = s.expand(sum(m[i][c]*m[j][c] for i,j,c in pairs))
        F = s.expand(sum(2*(f[i][c]*m[j][c]+m[i][c]*f[j][c])/(r[i]+r[j]) for i,j,c in pairs)/4)
        check('real_trace_derivative', s.expand(s.diff(C,t)-4*F+2*H)==0)
        check('coherent_fold', s.expand(H-sum(sum(m[i][c] for i in range(size))**2 for c in range(6)))==0)
        check('real_trace_FTC', s.expand(4*s.integrate(F,(t,0,1))-C.subs(t,1)+C.subs(t,0)-2*s.integrate(H,(t,0,1)))==0)

# Literal nonsplit complementary two-plane middle star.
a,b,theta = s.symbols('a b theta')
ht = theta**3+theta**2-2*theta-1
G = s.groebner([a*b-2+theta,ht],a,b,theta,domain=s.QQ)
J = s.Matrix([[0,-b],[a,0]])
R = theta*s.eye(2)/2+(1-theta-theta**2)*J/2
check('Hodge_norm_certificate', s.expand(theta**2+(1-theta-theta**2)**2*(2-theta)-4-(-theta**2+theta+2)*ht)==0)
for x in [R.det()-1,R.trace()-theta,*list(R*R-theta*R+s.eye(2)),*list(R**7-s.eye(2)),*list(R**4-R**3-J)]:
    check('Hodge_block', G.reduce(s.expand(x))[1]==0)

# Exact elliptic curve example over Q(i); illustrative, not all local places.
I=s.I
O=None
P=(s.S(0),s.S(0))
Qh=(I,1-I)

def add(A,B):
    if A is None: return B
    if B is None: return A
    x,y=A; X,Y=B
    if s.simplify(x-X)==0 and s.simplify(y+Y)==0: return O
    q=s.simplify((3*x*x-1)/(2*y) if A==B else (Y-y)/(X-x))
    z=s.simplify(q*q-x-X)
    return z,s.simplify(q*(x-z)-y)

def conj(A):
    return None if A is None else tuple(s.conjugate(z) for z in A)

def neg(A):
    return None if A is None else (A[0],-A[1])

check('BSD_actual_elliptic_half', s.expand(Qh[1]**2-Qh[0]**3+Qh[0])==0 and add(Qh,Qh)==P)
d=add(conj(Qh),neg(Qh))
check('BSD_actual_elliptic_cocycle', d is not None and add(d,d)==O and add(d,conj(d))==O)
check('BSD_actual_elliptic_equivariance', conj(add(Qh,P))==add(conj(Qh),conj(P)))

for name,count in counts.items():
    print(name,count,'PASS')
print('TOTAL',sum(counts.values()),'PASS')
