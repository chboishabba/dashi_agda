#!/usr/bin/env python3
"""Oriented volume and isotropy discriminator; conditional mass formula.
Original DASHI OrientedThreeAxisBracket369Exact (TorqueTrialectic369Exact),
RightHandRule369Exact, CarrierHiggsMassReceipt and selected quotient Gram.
Classical cross product, Gram determinant and signed-permutation symmetry.
The Higgs Gram entries are inherited from a283c3e4, not recomputed here.
"""
import sympy as s
r,t=s.symbols('r t',real=True); D=1-r*r
G=s.Matrix([[1,r,0],[r,1,0],[0,0,D]])
assert s.expand(G.det()-D**2)==0
x=s.Matrix([1,0,0]); y=s.Matrix([r,t,0]); z=x.cross(y)
F=s.Matrix.hstack(x,y,z)
assert F.det()==t*t
assert y.cross(x)==-z
assert F.T*F==s.Matrix([[1,r,0],[r,r*r+t*t,0],[0,0,t*t]])
u,v=s.symbols('u v',real=True)
P=s.Matrix([[0,0,1],[1,0,0],[0,1,0]])
M=s.Matrix([[u,v,v],[v,u,v],[v,v,u]])
assert P.T*M*P==M
assert s.expand(M.charpoly().as_expr()-(M.charpoly().gen-u-2*v)*(M.charpoly().gen-u+v)**2)==0
S=s.diag(1,-1,-1); assert (S.T*M*S-M)[0,1]==-2*v
assert s.expand(G.charpoly().as_expr()-(G.charpoly().gen-1-r)*(G.charpoly().gen-1+r)*(G.charpoly().gen-D))==0
rho2=s.Rational(1616,13471)**2/(s.Rational(1526,13471)*s.Rational(238495303,76582635))
m0=(1+s.sqrt(5))/2*s.Rational('246.22')/s.pi
print('volume',s.N(1-rho2,16),'scale',s.N((1-rho2)**s.Rational(1,3),16),'mass',s.N(m0*(1-rho2)**s.Rational(1,3),16))
print('PASS cross completion, C3 counterexample, axis-sign isotropy condition')
# A mass operator has units mass; a Hessian has units mass squared.
# If a physical mass operator has determinant m0^3*D and is positive
# isotropic, its eigenvalue is m0*D^(1/3). The corresponding mass-square
# determinant must be m0^6*D^2, not m0^6*D.
# No physical equality between frame volume and mass determinant is proved.
# Cross completion uses a selected oriented Euclidean 3-space, not a
# canonical cross product on the 23-dimensional quotient.
print('OPEN physical signed-axis action, mass determinant law, vacuum and pole')
