"""Exact weighted-convolution controls; not native kernel or PDE acceptance."""
from fractions import Fraction as Q
from itertools import product
from random import Random
import sympy as s
if not __debug__:
    raise SystemExit('refuse optimized Python')
rng=Random(36929)
counts={}
def check(k,v):
    if not v: raise AssertionError(k)
    counts[k]=counts.get(k,0)+1

def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def norm2(a): return sum(x*x for x in a)
# Finite zero-extended amplitudes; reciprocal weight restricted to their
# common support for this discrete exact reference, no cyclic wraparound.
S=list(product(range(-1,2),repeat=3))
O=list(product(range(-2,3),repeat=3))
for _ in range(16):
    R=Q(rng.randint(1,5),3)
    w={k:Q(rng.randrange(0,8),7) for k in S}
    W={k:R*R+norm2(k) for k in S}
    A={k:w[k]**2*W[k] for k in S}
    B={k:1/W[k] for k in S}
    conv=lambda f,x:sum(a*f.get(sub(x,k),0) for k,a in f.items())
    M=sum(A.values()); BB=sum(b*b for b in B.values())
    SC=SA=SM=Q(0)
    for x in O:
        c,a,b=conv(w,x),conv(A,x),conv(B,x)
        check('weighted_fibre',c*c<=a*b<=a*BB)
        check('energy_fibre',c<=sum(z*z for z in w.values()))
        p=[v*w.get(sub(x,k),0) for k,v in w.items()]
        m=sum(u*v for u in p for v in p)
        check('full_nine_coordinate_product',m==c*c)
        SC+=c*c; SA+=a; SM+=m
    check('convolution_mass',SA==M*M)
    check('global_weighted_bound',SC<=BB*M*M)
    check('global_product_factorization',SM==SC)
# Actual radial integral and optimized constant (analytic scalar control).
r,R,E,D=s.symbols('r R E D',positive=True)
B=s.integrate(4*s.pi*r*r/(R*R+r*r)**2,(r,0,s.oo))
check('radial_inverse_weight',s.simplify(B-s.pi**2/R)==0)
f=B*(R*R*E+D)**2
R0=s.sqrt(D/(3*E))
check('optimal_weight_stationary',s.simplify(s.diff(f,R).subs(R,R0))==0)
check('optimized_constant',s.simplify(f.subs(R,R0)-16*s.pi**2/(3*s.sqrt(3))*s.sqrt(E)*D**s.Rational(3,2))==0)
for k,v in counts.items(): print(k,v,'PASS')
print('TOTAL',sum(counts.values()),'PASS')
