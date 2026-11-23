import sympy as s
p,q,a,b,k,e,h=s.symbols('p q a b k e h', real=True)
G=(a+b)*(p+q)/4+k*(p+q)*(p*p+q*q)/4
V=e*(q-p)/h+G
# Strict monotonicity certificate for positive coefficients and timestep.
assert s.expand(s.diff(V,q)-e/h-(a+b)/4-k*((p+q)**2+2*q*q)/4)==0
R=s.Rational
count=1
for p0 in map(R,[-1,0,1]):
 for v0 in map(R,[-2,0,2]):
  params={p:p0,a:R(2),b:R(3),k:R(1,2),e:R(1,3),h:R(1,5)}
  poly=s.Poly(V.subs(params)-v0,q)
  roots=poly.intervals(eps=R(1,10**12))
  assert len(roots)==1 and roots[0][1]==1
  lo,hi=roots[0][0]
  assert poly.eval(lo)<=0<=poly.eval(hi)
  count+=2
print(f'{count} checks passed; SymPy {s.__version__}')
