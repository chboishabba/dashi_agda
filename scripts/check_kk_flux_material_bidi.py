import sympy as s
# AKW 2017 eqs 11,12,14,B7, tree limit c=0, instantons=0.
r,t,kappa,ell=s.symbols('r t kappa ell',positive=True)
e,h,e0,b,z=s.symbols('e h e0 b z',real=True)
EK=3/(4*kappa*t**3); gi=4*t*t/3; Ki=3*s.I/(2*t)
A=e0+e*b-h*z; E=A+s.I*e*t
R2=2*r/ell; U=2*ell
abs2=lambda x:s.expand(x*s.conjugate(x))
V=s.factor(EK/(4*r*r)*(2*abs2(E)/(1-2*r/(R2*U))+gi*abs2(e+E*Ki)-3*abs2(E)+4*R2*h*h*(gi*abs2(Ki)-1-4*r/(R2*U))))
expected=EK/(4*r*r)*(4*A*A+s.Rational(4,3)*e*e*t*t+8*r*h*h/ell)
assert s.simplify(V-expected)==0
assert s.simplify(r*s.diff(V,r)+V+EK/(4*r*r)*(4*A*A+s.Rational(4,3)*e*e*t*t))==0
print('tree flux potential:',V)
print('dilaton derivative strictly negative for nonzero h or e; axion Hessian rank one')
assert s.hessian(V,(b,z)).det().simplify()==0
# Material port: existing Filsinger constitutive equation eta Pdot=E-P/chi-beta P^3.
P,chi,beta,F,eta,Lam=s.symbols('P chi beta F eta Lam',positive=True)
W=P**2/(2*chi)+beta*P**4/4-F*P
assert s.diff(W,P)==P/chi+beta*P**3-F
# A gauge invariant dielectric function depending on neutral scalar z is a candidate coupling, not derived from the apparatus.
q=s.symbols('q',real=True)
W2=W+Lam*q*P**2/2
assert s.diff(W2,q)==Lam*P**2/2
# eliminate stable P locally: Schur complement produces negative curvature.
curv=1/chi+3*beta*P**2+Lam*q
assert s.diff(W2,q,P)==Lam*P
print('material Schur correction:',-Lam**2*P**2/curv)
print('PASS exact published tree-limit substitution, runaway identity, axion rank, nonlinear material derivative')
