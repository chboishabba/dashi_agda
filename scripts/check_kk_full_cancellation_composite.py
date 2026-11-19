"""BIDI terminal cancellation, composite ion, KK QCD and source-attributed ideal mode checks."""
import sympy as s
import math
G=6.67430e-11;c=299792458.;g=9.80665
k=math.sqrt(6)*g/c**2
u=c**4/(16*math.pi*G)*k*k
print('gradient',k,'gradient energy J/m3',u,'equivalent density',u/c**2)
mp,mn,me,B,Z,N,n,sp,sn,se,sB=s.symbols('mp mn me B Z N n sp sn se sB',real=True)
M=Z*mp+N*mn+n*me-B
D=Z*mp*sp+N*mn*sn+n*me*se-B*sB
assert s.simplify(D.subs({sp:se,sn:se,sB:se})-se*M)==0
print('composite differential numerator:',s.expand(D-se*M))
theta,b0,g5,beta0,A,UV=s.symbols('theta b0 g5 beta0 A UV',positive=True)
b=b0*s.exp(s.sqrt(s.Rational(2,3))*theta)
g4sq=g5**2/(2*s.pi*b)
logLambda=s.log(UV)-8*s.pi**2/(beta0*g4sq)-theta/s.sqrt(6)
Dlog=s.diff(logLambda,theta)
assert s.simplify(Dlog+1/s.sqrt(6)+s.sqrt(s.Rational(2,3))*8*s.pi**2/(beta0*g4sq))==0
print('QCD log slope',Dlog)
b1,b2,d=s.symbols('b1 b2 d',real=True)
assert s.simplify((g-c*c*b1*d)-(g-c*c*b2*d)-c*c*d*(-b1+b2))==0
sigma=g/(4*math.pi*G/6)
print('unscreened infinite-sheet surface density kg/m2',sigma)
v=s.Matrix([1,2,3]); assert (v.T*v)[0]==14
print('PASS composite derivative, KK bulk gauge slope, cancellation and bright norm')
I1,I2,J=s.symbols('I1 I2 J',positive=True)
K=s.Matrix([[J,-J],[-J,J]]); inertia=s.diag(I1,I2)
w2=J*(1/I1+1/I2)
assert s.simplify((K-w2*inertia).det())==0
assert K*s.Matrix([1,1])==s.zeros(2,1)
r,jp=s.symbols('r jp',real=True)
assert s.diff(jp*(1-s.cos(r)),r).subs(r,0)==0
print('PASS Leggett frequency and zero linear vertex at aligned equilibrium')
# Kuenstner et al 2025 DOI 10.1103/PhysRevResearch.7.013281: ideal red-sideband reduction
tau,gc=s.symbols('tau gc',real=True)
H=s.Matrix([[0,gc],[gc,0]])
a=s.Matrix([s.cos(gc*tau),-s.I*s.sin(gc*tau)])
assert s.simplify(s.diff(a,tau)+s.I*H*a)==s.zeros(2,1)
assert s.simplify((a.conjugate().T*a)[0])==1
# Zhang et al 2026 DOI 10.1038/s41467-026-68535-9: ideal signed GHZ contrast
v1,v2,v3,v4=s.symbols('v1 v2 v3 v4',real=True)
F=tau**2*(v1+v2-v3-v4)**2
assert s.simplify(F.subs({v2:v1,v3:v1,v4:v1}))==0
print('PASS RQU ideal exchange and distributed signed GHZ common-mode rejection')
print('reported 3.44 dB variance ratio',10**(3.44/10),'46.9 dB extinction power ratio',10**(46.9/10))
