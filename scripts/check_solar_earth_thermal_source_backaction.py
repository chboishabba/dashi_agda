"""Conditional small-signal thermal/electrojet closure; no calibrated parameters."""
import sympy as s
T,C,k,w,n,m,nu,b,q=s.symbols("T C k w n m nu b q",positive=True,real=True)
a,g,R,L,V,I=s.symbols("a g R L V I",positive=True,real=True)
# Source-backed thermal relaxation law, linearized about a stationary state.
H=1/(k+s.I*w*C)
assert s.simplify(H*s.conjugate(H)-1/(k*k+w*w*C*C))==0
# Signed Hall/Pedersen sensitivity with fixed population.
P=n*q*q*m*nu/((m*nu)**2+b*b)
D=s.diff(P,nu)
assert s.simplify(D-n*q*q*m*(b*b-m*m*nu*nu)/((m*nu)**2+b*b)**2)==0
# Finite natural generator, not prescribed local electric field.
# V = (R+1/g)*I; first-order current response to conductance perturbation.
i=V*g/(1+R*g)
assert s.simplify(s.diff(i,g)-V/(1+R*g)**2)==0
# DC source -> time-varying resistance: exact instantaneous power accounting.
assert s.simplify(V*i-R*i*i-i*i/g)==0
# Dynamic series inductance, linearized about i; g variation couples natural bias.
Z=R+1/g+s.I*w*L
K=i/g**2/Z
assert s.simplify(K.subs(w,0)-s.diff(i,g))==0
assert K.subs(V,0)==0
# Fourier mixing retains DC and both signed sidebands.
x=s.symbols("x",nonzero); d,e,f,h=s.symbols("d e f h",real=True)
mix=s.expand((g+d*x+e/x)*(V+f*x+h/x))
assert mix.coeff(x,0)==g*V+d*h+e*f
assert mix.coeff(x,2)==d*f and mix.coeff(x,-2)==e*h
# Reverse amplitude bound for a selected linearized receiver gain.
M,u=s.symbols("M u",positive=True)
gain2=M*M*a*a*(K*s.conjugate(K))*(H*s.conjugate(H))
assert s.simplify(gain2-M*M*a*a*i*i/(g**4*((R+1/g)**2+w*w*L*L)*(k*k+w*w*C*C)))==0
print("PASS: 10 conditional symbolic assertions; physical_admission=False")
