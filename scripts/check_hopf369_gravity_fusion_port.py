#!/usr/bin/env python3
"""Classical Hopf-CS/BPST transgression and same-field MHD stress/work cuts."""
import sympy as s
x,y,z=s.symbols('x y z',real=True)
X=(x,y,z); D=1+x*x+y*y+z*z
r,L,rho,g,mu,c,G,b=s.symbols('r L rho g mu c G b',positive=True)
F=lambda v:s.factor(s.cancel(v))
clean=lambda v:v.applyfunc(F)
def grad(v):return s.Matrix([s.diff(v,j) for j in X])
def curl(v):return clean(s.Matrix([s.diff(v[2],y)-s.diff(v[1],z),s.diff(v[0],z)-s.diff(v[2],x),s.diff(v[1],x)-s.diff(v[0],y)]))
def div(v):return F(sum(s.diff(v[i],X[i]) for i in range(3)))
checks=[]
def eq(name,a,b):
    d=a-b
    assert (clean(d)==s.zeros(*d.shape) if isinstance(d,s.MatrixBase) else s.simplify(d)==0),name
    checks.append(name)
a,h,k,d=s.Matrix([2*x,2*y,2*z,D-2])/D
v=s.Matrix([h,k,d])
R=s.Matrix.hstack(*[clean(a*v.diff(j)-s.diff(a,j)*v+v.cross(v.diff(j))) for j in X])
A=R.row(0).T; B=curl(A); J=curl(B)
eq('Hopf orientation volume',A.dot(B),2*R.det())
eq('Hopf density',A.dot(B),16/D**3)
eq('div B',div(B),0)
for i,j in [(0,1),(1,2),(2,0)]:eq('MC',R[:,j].diff(X[i])-R[:,i].diff(X[j]),2*R[:,i].cross(R[:,j]))
# trace fundamental SU2 imaginary quaternions: tr(e_i e_j e_k)=-2 epsilon.
I=s.I; e=[s.Matrix([[I,0],[0,-I]]),s.Matrix([[0,1],[-1,0]]),s.Matrix([[0,I],[I,0]])]
for i in range(3):
 for j in range(3):
  eq('trace2',s.trace(e[i]*e[j]),-2*int(i==j))
  for k in range(3):eq('trace3',s.trace(e[i]*e[j]*e[k]),-2*s.LeviCivita(i,j,k))
# R=dq q^-1, C=-f R. tr CS(-R)=tr R^3/3=-2 A wedge dA.
eq('CS density',-12*R.det()/3,-2*A.dot(B))
rad=lambda power,coeff:s.integrate(4*s.pi*r*r*coeff/(1+r*r)**power,(r,0,s.oo))
eq('CS charge',rad(3,32)/(8*s.pi**2),1)
f=r*r/(r*r+rho*rho)
eq('selfdual radial ODE',r*s.diff(f,r),2*f*(1-f))
eq('transgression coefficient',s.integrate(2*s.diff(f,r)*f*(1-f),(r,0,s.oo)),s.Rational(1,3))
eq('BPST energy',2*s.pi**2*s.integrate(r**3*192*rho**4/(r*r+rho*rho)**4,(r,0,s.oo))/(4*g*g),8*s.pi**2/g**2)
# MHD normalized Alfvén units; subtract constant background pressure only.
for sign in (-1,1):
 u=sign*B; p=-B.dot(B)/2
 stress=u*u.T-B*B.T+(p+B.dot(B)/2)*s.eye(3)
 E=-u.cross(B); S=E.cross(B)
 eq('total momentum flux perturbation',stress,s.zeros(3));eq('ideal electric field',E,s.zeros(3,1));eq('Poynting',S,s.zeros(3,1));eq('current work',J.dot(E),0)
 eq('momentum nonzero',u.dot(u),64/D**4)
eq('MHD energy density',B.dot(B),64/D**4)
eq('MHD energy integral',rad(4,64),8*s.pi**2)
# Dimensional energy proxy, not full GR source. Positive spherical Poisson source.
energy=8*s.pi**2*b*b*L**3/mu
U=64*b*b/(mu*(1+(r/L)**2)**4)
eq('energy density integral',rad(4,64)*b*b*L**3/mu,energy)
eq('mass equivalent positive formula',energy/c**2,8*s.pi**2*b*b*L**3/(mu*c**2))
# A separate time-dependent rigid translation gives E=-V cross B and
# S = V B^2 - B(V.B), unlike the aligned stationary field.
V=s.Matrix(s.symbols('Vx Vy Vz',real=True)); Et=-V.cross(B)
eq('translation induction',curl(V.cross(B)),-B.jacobian(X)*V)
eq('translation flux',Et.cross(B),V*B.dot(B)-B*V.dot(B))
print(f'{len(checks)}/{len(checks)} PASS; SymPy {s.__version__}')
