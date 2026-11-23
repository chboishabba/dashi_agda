import sympy as s
import numpy as np
from scipy.integrate import quad
# Covariant two scalar EFT, reference scalar Z supplies material orientation.
# L=-1/2 K (grad phi)^2 -1/2 M (grad X)^2 -1/2 H (grad Z)^2 + lambda X grad Z.grad phi - U(X)
K,M,H,l,X,D,g=s.symbols('K M H l X D g', real=True)
a=s.symbols('a:4',real=True); b=s.symbols('b:4',real=True); z=s.symbols('z:4',real=True)
h=s.symbols('h:4',real=True,nonzero=True)
U=D*X**2/2+g*X**4/4
L=-sum(h[i]*(K*a[i]**2+M*b[i]**2+H*z[i]**2-2*l*X*a[i]*z[i])/2 for i in range(4))-U
# diagonal metric variation of sqrt(-g) L
T=[s.expand(-2*s.diff(L,h[i])+L/h[i]).subs(dict(zip(h,[-1,1,1,1]))) for i in range(4)]
active=s.expand(sum(T)); assert s.simplify(active-(2*K*a[0]**2+2*M*b[0]**2+2*H*z[0]**2-4*l*X*a[0]*z[0]-2*U))==0
print('active stress:',active)
assert s.simplify(active.subs({a[0]:0,b[0]:0,z[0]:0})+2*U)==0
print('static gradient cancellation in active contraction; potential remains')
# Exact finite duration inverse control, fixed quartic, endpoints at X=-1,+1.
t=s.symbols('t',real=True); x=-1+2*(10*t**3-15*t**4+6*t**5); v=s.diff(x,t); acc=s.diff(v,t)
delta=-1; gamma=1; mass=1; eta=s.Rational(1,10)
B=s.expand(mass*acc+eta*v+delta*x+gamma*x**3)
assert all(v.subs(t,i)==0 and acc.subs(t,i)==0 and B.subs(t,i)==0 for i in (0,1))
work=s.integrate(B*v,(t,0,1)); heat=s.integrate(eta*v*v,(t,0,1)); assert work==heat
print('exact switching work',work,'heat',heat,'storage difference 0')
print('PASS metric variation, static source, inverse trajectory and work')
# Positive completion, keeping the cross vertex, requires an X-dependent diagonal term.
H0=s.symbols('H0',positive=True)
G=s.Matrix([[K,-l*X],[-l*X,H0+l*l*X*X/K]])
assert s.simplify(G.det()-K*H0)==0
p,q=s.symbols('p q',real=True)
assert s.simplify((s.Matrix([p,q]).T*G*s.Matrix([p,q]))[0]-(K*(p-l*X*q/K)**2+H0*q*q))==0
print('PASS positive square completion for all X if K,H0>0')
# Same ambient bias throughout; drive and stiffness are independent controls.
B0=s.Rational(1,10); d0=-s.Rational(11,10); d1=-s.Rational(9,10)
shape=10*t**3-15*t**4+6*t**5
Dt=d0+(d1-d0)*shape
F=s.expand(mass*acc+eta*v+Dt*x+x**3-B0)
assert F.subs(t,0)==F.subs(t,1)==0
Wforce=s.integrate(F*v,(t,0,1)); Wmod=s.integrate(s.diff(Dt,t)*x*x/2,(t,0,1))
Es=lambda i: (Dt*x*x/2+x**4/4-B0*x).subs(t,i)
assert s.simplify(Wforce+Wmod-heat-(Es(1)-Es(0)))==0
print('fixed ambient bias: force work',Wforce,'stiffness work',Wmod,'heat',heat,'delta stored',Es(1)-Es(0))
