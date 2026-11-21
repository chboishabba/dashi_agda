import sympy as s
# Polynomial two-jet of the literal source implicit equation D=C(B-hD).
t=s.symbols('t'); a,b,c,d,e,f=s.symbols('a b c d e f'); B=s.Matrix([a,b,c]); H=s.Matrix([[1],[0],[0]]); M=s.Matrix([[1,2,3]])
assert M*H==s.eye(1)
C=lambda z: d*z[0]*z[1]+e*z[1]*z[2]+f*z[2]**2
D2=C(B); Phi=t*B-H*t**2*D2
assert s.expand(C(Phi)-t**2*D2).coeff(t,2)==0
assert s.expand((M*Phi)[0]+C(Phi)-t*(M*B)[0]).coeff(t,2)==0
# Fine lift H1 and its own nonlinear correction; scalar exact jet model.
J,K=s.symbols('J K'); u,v=s.symbols('u v'); H1=s.Matrix([[1,2,0],[0,1,1]]); j=s.Matrix([J,K]); Dfine=s.Matrix([u,v]); Hfine=s.Matrix([[1,0],[0,1]])
phi=H1*Phi-t**2*Hfine*Dfine
linear=(j.T*phi)[0]
assert s.expand(s.expand(linear).coeff(t,2)+(j.T*(H1*H*D2+Hfine*Dfine))[0])==0
# On tangent, first-order stationarity does not kill a quadratic normal correction.
Bt=B.subs(a,-2*b-3*c)
assert M*Bt==s.zeros(1,1)
assert s.expand(C(Bt))!=0
# Native side-13 wrapped selected Q0 has coefficient 1/N per bond direction.
N=13**4; L=13
# For L Q0, single-bond pivot and uniform section have different Euclidean cost.
pivot=s.Rational(N,L); uniform=s.Rational(1,L)
assert L*pivot/N==1 and L*uniform==1
assert pivot**2/(N*uniform**2)==N
# exact inherited margin, not a curvature measurement.
fW=s.Rational(1579499892025915936100626501,91687345185165225945115656192)
margin=fW-s.Rational(1,64)
assert margin>0
print('PASS: implicit source two-jet, fine-lift chain rule, tangent counterexample, pivot normalization; margin',margin)
