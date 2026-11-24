from hashlib import sha1
from pathlib import Path
import sympy as S

# Exact similarity chain rule, viscosity one, in three spatial coordinates.
t, T = S.symbols('t T', real=True)
x = S.symbols('x:3', real=True)
s, *y = S.symbols('s y:3', real=True)
# Use positive tau explicitly, with d/dt = -d/dtau.
tau = S.symbols('tau', positive=True)
W = S.Function('W')(s, *y)
sub = {s: -S.log(tau), **dict(zip(y, [z/S.sqrt(tau) for z in x]))}
u = tau**(-S.Rational(1, 2))*W.subs(sub, simultaneous=True)
expected = (S.diff(W, s)+W/2+sum(z*S.diff(W,z)/2 for z in y)).subs(sub, simultaneous=True)
assert S.simplify(-S.diff(u,tau)-tau**(-S.Rational(3,2))*expected)==0
for j in range(3):
    assert S.simplify(S.diff(u,x[j])-S.diff(W,y[j]).subs(sub, simultaneous=True)/tau)==0
    assert S.simplify(S.diff(u,x[j],2)-S.diff(W,y[j],2).subs(sub, simultaneous=True)/tau**S.Rational(3,2))==0
# Exact scaling exponents for the squared homogeneous Sobolev core.
a = S.symbols('a', real=True)
assert S.expand((1-2*a)/2-S.Rational(1,2)+a)==0
assert (S.Rational(1,2)-a).subs(a,S.Rational(1,4))==S.Rational(1,4)
assert (-S.Rational(1,2)+S.Rational(3,2)/3)==0
# Reflected chart, derivative joins at the physical interface.
z = S.symbols('z', real=True)
P = 2+3*z+5*z**2+7*z**3
Q = P.subs(z,-z)
for j in range(4):
    assert S.diff(P,z,j).subs(z,0)==(-1)**j*S.diff(Q,z,j).subs(z,0)
assert S.diff(P,z).subs(z,0)-S.diff(P.subs(z,-z),z).subs(z,0)==6
assert S.diff(S.Abs(z),z,2)==2*S.DiracDelta(z)
# The patched angular weight differs by |m|, including equality at zero.
m = S.symbols('m', real=True)
assert S.simplify((S.Abs(m)+S.Rational(1,2))**2-(m*m+S.Rational(1,4))-S.Abs(m))==0
print('PASS: 7 chain-rule, 3 scale, 6 join/distribution, 1 weight-patch checks')
print('Git blob:', sha1(b'blob '+str(len(Path(__file__).read_bytes())).encode()+b'\0'+Path(__file__).read_bytes()).hexdigest())
