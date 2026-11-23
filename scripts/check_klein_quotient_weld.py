from sympy import symbols, cancel, expand, I, Rational
from time import perf_counter
start=perf_counter()
a,b,e,d,c=symbols('a b e d c', nonzero=True)
Q=a*a-a*b+b*b; V=a*b*(b-a)
assert cancel((16*Q)**3/(16*V**2)-256*Q**3/V**2)==0
assert cancel((c**4*a)**3/(c**12*d)-a**3/d)==0
assert cancel((a+e)**3/(d+b)-a**3/d-((a+e)**3-a**3)/(d+b)+a**3*b/(d*(d+b)))==0
# Difference of inverse witnesses: d*u=d*v=1 => u-v=0 by field cancellation.
u,v=symbols('u v'); assert expand(u*(1-d*v)-v*(1-d*u)-(u-v))==0
count=0
for x in range(-8,9):
 for y in range(-8,9):
  if not x or not y or x==y: continue
  q=x*x-x*y+y*y; w=x*y*(y-x)
  assert Rational((16*q)**3,16*w*w)==Rational(256*q**3,w*w)
  count+=1
print('PASS 4 universal identities;',count,'exact quotient cases;',perf_counter()-start,'s')
