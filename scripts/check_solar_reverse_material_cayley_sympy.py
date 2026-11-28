"""Exact rational two-stage material/cayley/work/restoration tangent audit.
Independent finite model; not a real spherical original-data execution.
"""
import sympy as s
z=s.symbols('z',real=True); h=s.Rational(1,4)
D=s.Rational(9,4)+z/8
nu=s.Rational(1,3)+z/10
heat=s.Rational(1,5)+z/3
T0=s.Rational(3,2);cool=s.Rational(1,2);cap=s.Rational(2)
Ta=s.exp(-h*cool/cap);Tb=(1-Ta)/cool
T=Ta*T0+Tb*heat
assert s.simplify(s.diff(T,z)-Tb/3)==0
W=s.Rational(3,5);mass=s.Rational(5,4);vol=s.Rational(3,2)
c=W*s.sqrt(D/vol)/s.sqrt(mass)
dc=W/s.sqrt(mass)*s.diff(D,z)/(2*s.sqrt(D*vol))
assert s.simplify(s.diff(c,z)-dc)==0
A=s.Matrix([[-s.Rational(1,2),-c],[c,-nu]])
dA=s.Matrix([[0,-dc],[dc,-s.Rational(1,10)]])
assert A+A.T==s.diag(-1,-2*nu)
assert dA+dA.T==s.diag(0,-s.Rational(1,5))
source=s.Matrix([s.Rational(1,2),0]);inc=s.Rational(1,3)
x0=s.zeros(2,1);dx0=s.zeros(2,1)
K=s.eye(2)-h*A/2;P=s.eye(2)+h*A/2
x1=K.inv()*(P*x0+2*h*inc*source)
m1=(x0+x1)/2
dx1=K.inv()*(P*dx0+h*dA*m1)
assert all(s.simplify(v)==0 for v in dx1-x1.diff(z))
x2=K.inv()*(P*x1+2*h*inc*source)
m2=(x1+x2)/2
dx2=K.inv()*(P*dx1+h*dA*m2)
assert all(s.simplify(v)==0 for v in dx2-x2.diff(z))
load=s.Rational(1,2)
useful=h*load*(m1[0]**2+m2[0]**2)
duseful=2*h*load*(m1[0]*s.diff(m1[0],z)+m2[0]*s.diff(m2[0],z))
assert s.simplify(s.diff(useful,z)-duseful)==0
R=x2.dot(x2);dR=2*x2.dot(dx2)
assert s.simplify(s.diff(R,z)-dR)==0
bad=s.Matrix([[0,dc],[dc,0]])
assert bad+bad.T!=s.zeros(2)
point=s.Rational(1,4)
assert all(s.simplify(expr.subs(z,point))==0 for expr in
    [s.diff(useful,z)-duseful,s.diff(R,z)-dR])
print(dict(sympy=s.__version__,assertion_groups=12,
    two_stage_memory=True,reciprocity=True,
    work_tangent=True,terminal_restoration_jvp=True))
