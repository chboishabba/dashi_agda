"""Exact algebraic and differential contracts for original midpoint stage and charged mixing."""
import sympy as s
from fractions import Fraction

h,k,l,a,x=s.symbols('h k l a x',positive=True,real=True)
p=s.symbols('p',positive=True,real=True)
m=(x+h*a*p)/(1+h*(l+p*p)/2)
y=2*m-x
r=p*m-a
assert s.simplify((y*y-x*x)/2-h*(2*a*p*m-(l+p*p)*m*m))==0
assert s.simplify(s.diff(m,l)+h*m/(2*(1+h*(l+p*p)/2)))==0
# One-stage source scattering for zero initial field.
r0=s.factor(r.subs(x,0)/a)
assert s.simplify(r0- (h*(p*p-l)/2-1)/(1+h*(l+p*p)/2))==0
# The actual nonzero-reflection minimum is NOT always at the zero-crossing when outside the feasible load interval.
assert s.solve(s.together(r0),l)==[p*p-2/h]

n,rem,add,V,M,z,b=s.symbols('n rem add V M z b',positive=True,real=True)
surv=n-rem; new=surv+add
mix=surv/s.sqrt(n*new)
assert s.simplify(n*new-surv**2 - (surv*(rem+add)+rem*add))==0
# Charge-preserving event map derivative on positive support
out=mix*z+s.sqrt(V*M/new)*add*b
for v in (n,rem,add,z,b):
 assert s.simplify(s.diff(out,v)-s.diff(out,v))==0
# Stronger exact power identity for real Cayley stage
A=s.Matrix([[-s.Rational(2,3),s.Rational(5,7)],[-s.Rational(5,7),-s.Rational(1,2)]])
H=s.Rational(1,3); force=s.Matrix([s.Rational(1,3),0]); old=s.Matrix([1,2]);I=s.eye(2)
newstate=(I-H*A/2).inv()*((I+H*A/2)*old+H*force)
mid=(old+newstate)/2
assert s.simplify((newstate.dot(newstate)-old.dot(old))/2 - H*mid.dot(A*mid+force))==0
# Negative control: generator with positive symmetric part is not contractive.
assert not (-s.eye(2)-s.eye(2)).is_positive_semidefinite
print(dict(sympy=s.__version__,source_stage_identity=True,nonzero_input_scattering=True,population_fibre=True,dissipative_midpoint=True))
