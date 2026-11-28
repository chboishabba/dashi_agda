"""Exact algebra controls; not native kernel or Clay endpoint acceptance."""
import itertools as it
import random
from fractions import Fraction as Q
import sympy as s

if not __debug__:
    raise SystemExit('refuse optimized Python: assertion gates disabled')

rng = random.Random(369)
counts = {}

def check(name, ok):
    if not ok:
        raise AssertionError(name)
    counts[name] = counts.get(name, 0) + 1

def dot(a, b):
    return sum(x*y for x, y in zip(a, b))

def cross(a, b):
    return (a[1]*b[2]-a[2]*b[1], a[2]*b[0]-a[0]*b[2], a[0]*b[1]-a[1]*b[0])

def vec():
    return tuple(rng.randint(-4, 4) for _ in range(3))

def mass(a):
    return dot(a, a)

for _ in range(512):
    eta, xi = vec(), vec()
    ur, ui = cross(eta, vec()), cross(eta, vec())
    mid = tuple(Q(a)-Q(b, 2) for a, b in zip(eta, xi))
    zeta = tuple(b-a for a, b in zip(eta, xi))
    pm = mass(ur)+mass(ui)
    pd = dot(xi, ur)**2+dot(xi, ui)**2
    bound = min(mass(xi)*pm, 4*mass(mid)*pm)
    rate = mass(eta)+mass(zeta)
    check('NS_phase_midpoint', dot(eta, ur)==dot(eta, ui)==0 and pd<=bound and rate==Q(mass(xi), 2)+2*mass(mid))
    if rate:
        nu=Q(3, 7)
        check('NS_resolvent', Q(pd)/(nu*rate)<=bound/(nu*(Q(mass(xi),2)+2*mass(mid))))
    perm = (1,2,0)
    rot=lambda a: tuple(a[i] for i in perm)
    check('NS_C3_phase', cross(rot(eta),rot(ur))==rot(cross(eta,ur)) and dot(rot(xi),rot(ur))==dot(xi,ur))

for _ in range(128):
    w=[Q(rng.randint(0,7),7) for _ in range(9)]
    f=[Q(rng.randint(-20,20),3) for _ in w]
    g=[Q(rng.randint(-20,20),5) for _ in w]
    e=[abs(a-b) for a,b in zip(f,g)]
    check('signed_step_measure', abs(dot(w,f)-dot(w,g))<=dot(w,e))

# Algebra-only model of equivariant cochain transport, not an elliptic curve.
for q, sig in it.product(range(12),(-1,1)):
    f=lambda x: (2*x)%24
    check('BSD_cochain_algebra', f((sig*q-q)%12)==(sig*f(q)-f(q))%24 and f((2*q)%12)==2*f(q)%24)

t,j=s.symbols('t j')
G=s.groebner([t**3+t**2-2*t-1,j*j-t+2],j,t,domain=s.QQ)
r=(t+(1-t-t*t)*j)/2
for expr in [r**2-t*r+1,r**7-1,r**4-r**3-j]:
    check('Hodge_cyclotomic', G.reduce(s.expand(expr))[1]==0)

for m in range(17):
    for n in range(9):
        for bs in it.product((0,1),repeat=n):
            x=y=0
            for b in bs:
                x=2*x+b
                y=min(m,2*y+b)
                check('PNP_binary_prefix', y==min(m,x))

# Original F19 shared plaquette mixed log derivatives on the stated slice.
a,b,N,beta=s.symbols('a b N beta',positive=True)
W=-beta*2/N*(11*(1-s.cos(a))+11*(1-s.cos(b))+1-s.cos(b-a))
for m,n in it.product(range(1,7),repeat=2):
    got=s.diff(W,a,m,b,n).subs({a:0,b:0})
    want=0 if (m+n)%2 else 2*beta/N*(-1)**(m+(m+n)//2)
    check('YM_F19_mixed',s.simplify(got-want)==0)

for _ in range(128):
    a,b,c=vec(),vec(),vec()
    p=(1,2,0)
    rot=lambda v: tuple(v[i] for i in p)
    check('RH_determinant_C3',dot(a,cross(b,c))==dot(rot(a),cross(rot(b),rot(c))))

for k,v in counts.items():
    print(k,v,'PASS')
print('TOTAL',sum(counts.values()),'PASS')
