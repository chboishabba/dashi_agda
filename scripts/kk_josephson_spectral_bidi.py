import sympy as s
q,J,C,F,n=s.symbols('q J C F n', positive=True)
u,v=s.symbols('u v', real=True)
# Two charge states, detuning F; q-dependent tunnelling and charging.
x=s.symbols('x',real=True)
H=s.Matrix([[x,-J/2],[-J/2,-x]])
E=-s.sqrt(x*x+J*J/4)
assert s.simplify(E.diff(x,2)+J**2/(4*(x*x+J*J/4)**s.Rational(3,2)))==0
assert s.simplify(E.diff(x,2).subs(x,0)+2/J)==0
assert s.simplify(E.series(x,0,6).removeO()-(-J/2-x*x/J+x**4/J**3))==0
# Heisenberg Killing vectors in asymmetric UH coordinates
D,X,Z,p=s.symbols('D X Z p',real=True); coords=(D,X,Z,p)
a=s.exp(-D); G=s.Matrix([[1,0,0,0],[0,a,0,0],[0,0,a+a*a*X*X,-a*a*X],[0,0,-a*a*X,a*a]])
ks=[s.Matrix([0,1,0,Z]),s.Matrix([0,0,1,0]),s.Matrix([0,0,0,1])]
for k in ks:
 A=k.jacobian(coords); L=sum((k[i]*G.diff(coords[i]) for i in range(4)),s.zeros(4))+A.T*G+G*A
 assert s.simplify(L)==s.zeros(4)
assert ks[1].jacobian(coords)*ks[0]-ks[0].jacobian(coords)*ks[1]==-ks[2]
print('PASS three actual UH Killing vectors and central bracket')
# Physical charge dipole d times electric field, E0=-sqrt((dE)^2+J²/4).
d=s.symbols('d',positive=True); field=s.symbols('field',real=True)
energy=E.subs(x,d*field); chi=-energy.diff(field,2).subs(field,0)
assert s.simplify(chi-2*d*d/J)==0
# Legendre transform to polarization variable
P=s.symbols('P',real=True); W=-J/2*s.sqrt(1-P*P/d**2)
assert s.simplify(W.series(P,0,6).removeO()-(-J/2+J*P**2/(4*d*d)+J*P**4/(16*d**4)))==0
print('PASS exact two-charge susceptibility',chi,'and nonlinear Legendre potential',W)
# Same scalar dependence from a selected exponential tunneling and dipole law
J0,d0=s.symbols('J0 d0',positive=True); A,B=s.symbols('A B',real=True)
invchi=J0*s.exp(A*q)/(2*d0*d0*s.exp(2*B*q))
assert s.simplify(invchi.diff(q)-(A-2*B)*invchi)==0
print('PASS modulus derivative = (d ln J - 2 d ln d) / chi')
