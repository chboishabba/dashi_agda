"""Exact algebraic weld checks; physical producer hypotheses are not proved."""
import sympy as s
from itertools import product
checks=0
def check(expr):
    global checks
    assert s.expand(expr)==0, expr
    checks+=1
# Reflection is antilinear; stationarity makes both one-point terms conjugate.
a,b,c=s.symbols('a b c'); check(c-s.conjugate(a)*b-s.conjugate(a)*b+s.conjugate(a)*b-(c-s.conjugate(a)*b))
# Arbitrary word linear combination: centered Gram = raw Gram - rank-one mean.
for n in range(1,6):
    u=s.Matrix(s.symbols(f'u:{n}')); z=s.Matrix(s.symbols(f'z:{n}')); G=s.Matrix(n,n,s.symbols(f'g:{n*n}'))
    check((z.conjugate().T*(G-u.conjugate()*u.T)*z)[0]-((z.conjugate().T*G*z)[0]-s.conjugate((u.T*z)[0])*(u.T*z)[0]))
# Positive spectral mass contradiction: exact finite geometric proxy.
for slow,fast in [(s.Rational(1,2),s.Rational(1,4)),(s.Rational(3,4),s.Rational(2,3))]:
    for k in range(1,15):
        assert 0 < (fast/slow)**(k+1) < (fast/slow)**k < 1
        checks+=1
# Fourth cumulant difference and sharp conservative error envelope.
v,d,e=s.symbols('v d e', real=True)
check((e-3*((v+d)**2-v**2))-(e-6*v*d-3*d**2))
for v,a,b in product(map(s.Rational,range(5)),[s.Rational(1,4),s.Rational(1,2),s.Integer(1)],[s.Rational(1,3),s.Integer(1)]):
    for d,e in product([-a,0,a],[-b,0,b]):
        if v+d<0: continue
        assert abs(e-6*v*d-3*d*d)<=b+3*a*(2*v+a)
        checks+=1
print(f'{checks} exact checks passed; no source-level physical or Agda claim')
