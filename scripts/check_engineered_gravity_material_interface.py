"""Exact TOV surface and fixed-metric radial Hessian diagnostic.
Source: check_engineered_gravity_tov_material.py at 2909cb1695eb.
Not a coupled stability certificate.
"""
import sympy as s
x,l=s.symbols('x l',positive=True); p=l/(8*s.pi)
rho=(2+l)*p*(1-x); pr=-p*(1-x)**2
f=1-l*(2+l)*(x/3-x*x/5)
P=(2+l)*(s.Rational(1,3)-x/5)/2-(1-x)**2/2
pt=s.factor(pr+x*s.diff(pr,x)+x*l*(rho+pr)*P/(2*f))
a=s.factor((rho+pt)/2); d=s.factor((rho+pr)/(2*f)); V=s.factor(rho-2*a-d*f)
for name,z in [('a',a),('d',d),('V',V)]:
    assert s.cancel(z.subs(x,1))==0
    print(name,'surface quotient / p =',s.factor(s.cancel(z/(1-x)/p).subs(x,1)))
r,R,v=s.symbols('r R v',positive=True)
W=d.subs(x,R**2)*f.subs(x,r**2)*v**2+2*a.subs(x,R**2)*R**2/r**2+V.subs(x,R**2)
H=s.hessian(W,(R,v)).subs({R:r,v:1})
assert s.cancel(H[1,1]-2*d.subs(x,r*r)*f.subs(x,r*r))==0
print('PASS radial gradient Hessian identity')
e=s.symbols('e',positive=True)
E=s.integrate(1/(x*s.log(e)**2),(x,e**2,e))
assert s.simplify(E+1/s.log(e))==0
assert s.limit(E,e,0,dir='+')==0
print('PASS critical linear-weight trace counterexample')
