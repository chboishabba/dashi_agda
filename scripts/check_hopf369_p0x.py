"""P0X: original Hopf current penalty, AFZ profile, and brane probe algebra.
Exact symbolic/rational checks; no nonlinear PDE or physical experiment.
"""
import sympy as s
from math import gcd
checks=[]
def eq(name,a,b):
    d=a-b
    assert all(s.simplify(v)==0 for v in (list(d) if isinstance(d,s.MatrixBase) else [d])),name
    checks.append(name)
x,y,z=s.symbols('x y z',real=True); X=(x,y,z); D=1+x*x+y*y+z*z
A=2*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**2
curl=lambda a:s.Matrix([s.diff(a[2],y)-s.diff(a[1],z),s.diff(a[0],z)-s.diff(a[2],x),s.diff(a[1],x)-s.diff(a[0],y)])
B=4*A/D; J=curl(B); t0=4*(x*x+y*y)/D**2; d=(D-2)/D; l=2/D
V=s.Matrix([s.diff(t0,u) for u in X]).cross(B)
eq('original curl',curl(A),B)
eq('flux label',B.dot(s.Matrix([s.diff(t0,u) for u in X])),0)
eq('current density',J.dot(J),16*l**6+4*t0*l**4)
eq('cutoff derivative density',V.dot(V),16*l**6*t0*(1-t0))
eq('mixed current density',J.dot(V),8*l**5*d*t0)
t=s.symbols('t',real=True); h=s.Function('h')(t); hp=s.diff(h,t)
# d is the Cartesian S3 coordinate in the second complex plane:
# <d>=<d^3>=0, <d^2>=(1-t)/2.
q=s.symbols('q'); avg=lambda f:s.expand(f).subs(q**3,0).subs(q**2,(1-t)/2).subs(q,0)
raw=avg(16*(1-q)**3*h*h+4*t*(1-q)*h*h+16*(1-q)**2*q*t*h*hp+16*(1-q)**3*t*(1-t)*hp*hp)/4
reduced=(12-9*t)*h*h+2*t*(1-t)*(5-3*t)*hp*hp
eq('angular reduction modulo total derivative',raw-reduced,s.diff(-2*t*(1-t)*h*h,t))
# AFZ positive profile, exact constant flux and energy normalization.
p,q=s.symbols('p q',positive=True); K=p*p*(1-t)+q*q*t; c=p*q*(p+q)/2
f=q/(q-p)*(1-p/s.sqrt(K))
eq('AFZ derivative',s.diff(f,t),c/K**s.Rational(3,2))
eq('AFZ endpoints 0',f.subs(t,0),0);eq('AFZ endpoints 1',f.subs(t,1),1)
eq('AFZ squared first integral',K**3*(c/K**s.Rational(3,2))**2,c**2)
# Positive K in [0,1] is needed for the previous fractional-power identity.
for P,Q in [(3,2),(2,3),(2,2),(-3,2),(6,1),(-2,-2),(1,1)]:
    g=gcd(abs(P),abs(Q)); a,b=Q//g,P//g
    eq('signed primitive slope',P*a-Q*b,0)
    eq('total signed linking',g*g*a*b,P*Q)
# Rational Galerkin primal/dual certificate on original support tau=1/4.
tau=s.Rational(1,4); k=s.Rational(1,10)
w=1+k*(12-9*t); p=2*k*t*(1-t)*(5-3*t)
integ=lambda f:s.integrate(s.expand(f),(t,tau,1))
previous=None
for n in (2,4,8):
    basis=[(t-tau)**i for i in range(1,n+1)]
    # Moment integration is exact rational.
    M=s.Matrix(n,n,lambda i,j:integ(w*basis[i]*basis[j]+p*s.diff(basis[i],t)*s.diff(basis[j],t)))
    m=s.Matrix([integ(b) for b in basis]); u=M.inv()*m; lam=1/(m.dot(u)); coef=lam*u
    hn=s.expand(sum(coef[i]*basis[i] for i in range(n))); en=coef.dot(M*coef)
    eq('flux exact',integ(hn),1);eq('primal energy',en,lam)
    r=s.expand(lam-w*hn+s.diff(p*s.diff(hn,t),t))
    # w >= 1+3k, so this is an exact conservative dual bound.
    gap=integ(r*r)/(1+3*k)
    assert gap>=0 and (previous is None or en<=previous)
    checks.append('nested primal and positive dual gap');previous=en
    print('Galerkin',n,'lower',s.N(en-gap,16),'upper',s.N(en,16),'gap',s.N(gap,12))
# Pure graph probe: velocity Hessian at rest from original KK determinant.
T,Psi,S,ft=s.symbols('T Psi S ft',positive=True)
L=-T*Psi**3*s.sqrt(S-Psi**2*ft*ft)
eq('graph temporal Hessian',s.diff(L,ft,2).subs(ft,0),T*Psi**5/s.sqrt(S))
# Winding scalar stress in a spatial orthonormal frame, normal principal speeds.
T,a=s.symbols('T a',positive=True); om,kx,ky,kz=s.symbols('om kx ky kz',real=True)
Stress=s.diag(T+a,-T+a,-T-a,-T-a); cov=s.Matrix([om,kx,ky,kz])
eq('normal characteristic quadratic',cov.dot(Stress*cov),(T+a)*om**2-(T-a)*kx**2-(T+a)*(ky**2+kz**2))
eq('marginal winding direction',((T-a)/(T+a)).subs(a,T),0)
print(f'{len(checks)}/{len(checks)} exact assertions PASS; SymPy {s.__version__}')
