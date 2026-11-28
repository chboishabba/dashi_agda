import sympy as s
from fractions import Fraction as Q
from math import comb
n=s.symbols('n',integer=True,positive=True); z,xi,tau,v,D,N,q=s.symbols('z xi tau v D N q',positive=True)
x=s.symbols('x',real=True); p=n-s.Rational(1,2)
# wave in 1+2: 4q fqq+6 fq; coefficient from product z^-n
assert s.simplify(4*p*n*z**(-n)+4*p*(z-xi)*s.diff(z**(-n),z)-4*p*n*xi*z**(-n-1))==0
assert s.simplify(-s.diff(z**(1-n),z,2)+s.Rational(15,4)*z**(-n-1)-(s.Rational(15,4)-n*(n-1))*z**(-n-1))==0
# derivative source conormal q_xi-v q_tau = 2N; higher density regular
eta=s.symbols('eta',positive=True)
assert s.simplify(2*N*p*q**(p-1)/(4*z*xi)**n+(s.Rational(3,2)-n)/xi*q**p/(4*z*xi)**n-q**(-s.Rational(1,2))*((s.Rational(3,2)-n)*eta**n/xi+N*p*eta**(n-1)/(2*z*xi)).subs(eta,q/(4*z*xi)))==0
# leading weak derivative angular IBP
th=s.symbols('th',real=True); f=s.Function('f'); arg=x+D*s.cos(th)
assert s.expand(s.diff(s.sin(th)*s.Subs(s.Derivative(f(x),x),x,arg),th).doit()- (s.cos(th)*s.diff(f(x),x).subs(x,arg)-D*s.sin(th)**2*s.diff(f(x),x,2).subs(x,arg)))==0
# Abel normalization moments
for j in range(12):
 assert s.integrate(s.sin(th)**(2*j),(th,0,s.pi))/s.pi==s.Rational(comb(2*j,j),4**j)
print(s.__version__,'16 exact checks PASS')
# physical comoving detector: a(t)=t, directional scale a_i=t exp(e h/2)
t,e=s.symbols('t e',positive=True); h=s.Function('h')(t); ai=t*s.exp(e*h/2)
tidal=s.diff(-s.diff(ai,t,2)/ai,e).subs(e,0)
assert s.simplify(tidal+s.diff(h,t,2)/2+s.diff(h,t)/t)==0
# E4/SMS combination leaves explicit Laplacian channel
H1,H2,L,b=s.symbols('H1 H2 L b'); E=-b*b*(H2+L)/4; M=-b*b*(H2+2*H1-L)/2; R=-b*b*(H2+H1)/2
assert s.expand(R-E-M/2)==0
print('2 additional detector checks PASS')
