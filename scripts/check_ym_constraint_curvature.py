import sympy as s
# Exact constrained chart chain rule and sign discriminator.
t,x,y,l,k=s.symbols('t x y l k', real=True)
F=l*y+x*x/2
C=y-k*x*x/2
path={x:t,y:k*t*t/2}
assert s.diff(C.subs(path),t,2)==0
assert s.diff(F.subs(path),t,2)==1+l*k
assert (s.hessian(F,(x,y))-l*s.hessian(C,(x,y)))[0,0]==1+l*k
# A gauge-invariant scalar with a curved gauge slice: criticality on
# joint kernel alone does not eliminate gauge multiplier.
# Example has independent gauge direction y, averaging x+y.
A=s.Matrix([[1,1,0]]); G=s.Matrix([[0,1,0]]); g=s.Matrix([1,0,0])
assert A.T-G.T==g
# Native covariant divergence applied to a constant fine direction.
r=s.Rational(1,16384); a=(1-r*r)/(1+r*r); b=2*r/(1+r*r)
R=s.Matrix([[1,0,0],[0,a*a-b*b,2*a*b],[0,-2*a*b,a*a-b*b]])
assert R.T*R==s.eye(3)
assert (a-1)**2+b*b < s.Rational(1,4096)**2
v=s.Matrix([0,1,0]); residual=(s.eye(3)-R)*v
assert residual!=s.zeros(3,1)
# Uniform residual is killed by mean-zero projection, but not raw gauge.
P=s.eye(13)-s.ones(13)/13
assert P*s.ones(13,1)==s.zeros(13,1)
# exact inherited allowance, not an independently established source floor
f=s.Rational(1579499892025915936100626501,91687345185165225945115656192)
assert f-s.Rational(1,64)>0
print('PASS: chain rule, gauge multiplier discriminator, native-radius constant gauge residual, inherited allowance',f-s.Rational(1,64))
