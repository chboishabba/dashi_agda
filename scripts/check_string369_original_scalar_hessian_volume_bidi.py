#!/usr/bin/env python3
"""Original six-invariant E6/trinification restricted scalar Hessian BIDI.
Original #1106 Ternary27TrinificationInvariantTwoVEVPotentialExact and
#1241 check_kk_e6_orbifold_boundary_higgs_hessian.py.
Classical Schur complement and generalized mass determinant.
Restricted homogeneous comparison potential, NOT CY scalar action or
5D interval solution; Gram inserted as a separate conditional test.
"""
import sympy as s
x,y,z,t,l,r,k=s.symbols('x y z t l r k',real=True)
V=(x*x-1)**2+(y*y+z*z-1)**2+2*y*y*z*z+x*x*z*z
H0=s.hessian(V,(x,y,z)).subs({x:1,y:1,z:0})
assert H0==s.diag(8,8,6)
G=s.Matrix([[1,r,0],[r,1,0],[0,0,1-r*r]])
assert s.factor(H0.det()/G.det()-384/(1-r*r)**2)==0
assert s.expand((H0-k*G).det()-(8-k*(1+r))*(8-k*(1-r))*(6-k*(1-r*r)))==0
mu=3+(2*l-s.Rational(13,2))*t*t
Ve=V-mu*z*z+l*z**4
sub={x:s.sqrt(1-t*t/2),y:s.sqrt(1-2*t*t),z:t}
assert all(s.simplify(s.diff(Ve,q).subs(sub))==0 for q in (x,y,z))
H=s.simplify(s.hessian(Ve,(x,y,z)).subs(sub))
schur=s.simplify(H[2,2]-(H[2,:2]*H[:2,:2].inv()*H[:2,2])[0])
assert schur==t*t*(8*l-26)
assert s.factor(H.det()-64*t*t*(4*l-13)*(t*t-2)*(2*t*t-1))==0
# Actual relaxed branch, x²=1-z²/2 and y²=1-2z².
relaxed=s.expand(Ve.subs({x:s.sqrt(1-z*z/2),y:s.sqrt(1-2*z*z)}))
assert s.expand(relaxed-((3-mu)*z*z+(l-s.Rational(13,4))*z**4))==0
print('H0',H0,'relaxed potential',relaxed,'Schur',schur)
print('source restricted eigenvalues',H.subs({t:s.Rational('0.0246'),l:4}).evalf().eigenvals())
print('OPEN physical CY metric and potential weld, pole corrections, actual determinant law')
