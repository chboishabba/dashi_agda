"""Original peak-pulse central source NEC and conditional detector ceiling."""
import sympy as s
from fractions import Fraction as Q
u=s.symbols('u',positive=True); f=s.exp(1-1/(1-u*u))
F0=s.Rational(2,5)*(s.diff(f,u,4)+4*s.diff(f,u,3)/u)
assert s.limit(F0,u,0)==-24
b=s.symbols('b',positive=True); beta=s.sqrt(1+b*b)
v=-b/beta; amp=-6*s.sqrt(1-v*v)/b
assert s.simplify(-b*beta*amp/6)==1
K=b*b/(3*beta)
assert s.simplify(s.diff(K,b)-b*(2+b*b)/(3*beta**3))==0
assert s.simplify(K.subs(b,1)/24-s.sqrt(2)/144)==0
# sqrt(2)>1.414, upper bound for conditional normalized detector gain
assert Q('1.414')**2<2
assert Q('3.844e-182')/(72*Q('1.414'))<Q('3.776e-184')
print(s.__version__,'6 checks PASS; NEC central drive <=1/(72 sqrt(2))')
