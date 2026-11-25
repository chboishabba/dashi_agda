#!/usr/bin/env python3
"""Original noncompact Hopf KK vacuum data and Einstein-RMHD first jet.
Exact algebraic checks; not a spacetime evolution numerical solver.
"""
import sympy as s
checks=[]
def eq(name,a,b):
    d=a-b
    assert all(s.simplify(x)==0 for x in (list(d) if isinstance(d,s.MatrixBase) else [d])),name
    checks.append(name)
x,y,z=s.symbols('x y z',real=True); D=1+x*x+y*y+z*z
A=2*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**2
B=s.Matrix([s.diff(A[2],y)-s.diff(A[1],z),s.diff(A[0],z)-s.diff(A[2],x),s.diff(A[1],x)-s.diff(A[0],y)])
eq('original curl',B,4*A/D)
eq('original radial squared field',B.dot(B),64/D**4)
eq('original helicity density',A.dot(B),16/D**3)
r=s.symbols('r',nonnegative=True)
eq('original helicity integral',4*s.pi*s.integrate(16*r*r/(1+r*r)**3,(r,0,s.oo)),4*s.pi**2)
# In the connection frame [e_i,e_j]=-F_ij e_4. For the scalar
# and vertical Ricci entries all derivative contributions vanish.
f,g,h=s.symbols('f g h',real=True)
F=s.Matrix([[0,f,g],[-f,0,h],[-g,-h,0]])
Z=range(4)
structure=lambda i,j,k:-F[i,j] if i<3 and j<3 and k==3 else 0
Gamma=lambda i,j,k:(structure(i,j,k)-structure(j,k,i)+structure(k,i,j))/s.Integer(2)
for i in Z:
    for j in Z:
        for k in Z:
            eq('metric compatible',Gamma(i,j,k)+Gamma(i,k,j),0)
            eq('torsion free',Gamma(i,j,k)-Gamma(j,i,k),structure(i,j,k))
def curvature(i,j,k,l):
    return sum(Gamma(j,k,m)*Gamma(i,m,l)-Gamma(i,k,m)*Gamma(j,m,l)-structure(i,j,m)*Gamma(m,k,l) for m in Z)
# For nonconstant F, derivative pieces in these diagonal contractions
# vanish since Gamma(j,j,i)=Gamma(i,j,i)=0 identically.
for i in Z:
    for j in Z:
        eq('diagonal Ricci derivative coefficient 1',Gamma(j,j,i),0)
        eq('diagonal Ricci derivative coefficient 2',Gamma(i,j,i),0)
ric=[s.expand(sum(curvature(i,j,j,i) for i in Z)) for j in Z]
q=f*f+g*g+h*h
eq('seed vertical Ricci',ric[3],q/2)
eq('seed scalar',sum(ric),-q/2)
# Four-dimensional spatial conformal scalar formula R(psi^2 h)
# = psi^-3 (-6 Delta_h psi + R(h) psi).
eps=s.symbols('eps',positive=True); p=s.symbols('p',positive=True); grad2=s.symbols('grad2',nonnegative=True)
B2=s.symbols('B2',positive=True); lap=-eps**2*B2*p/12
eq('vacuum conformal constraint',(-6*lap-eps**2*B2*p/2)/p**3,0)
eq('radial Newton norm',s.integrate(64*r/(1+r*r)**4,(r,0,s.oo))/12,s.Rational(8,9))
eq('vertical conformal Ricci',eps**2*B2/2-lap/p-grad2,7*eps**2*B2/12-grad2)
eq('central vertical acceleration numerator',7*eps**2*64/12,s.Rational(112,3)*eps**2)
# Original stiff-fluid primitive differential in an orthonormal frame.
u=s.symbols('u',real=True); w,b=s.symbols('w b',positive=True); G2=1/(1-u*u)
J=s.Matrix([[2*G2-1,2*w*G2**2*u],[2*G2*u,w*G2**2*(1+u*u)]])
eq('parallel primitive determinant',J.det(),w*G2)
# Differentiate literal energy and momentum using arbitrary perturbations.
vx,vy,vz,bx,by,bz,P,C=s.symbols('vx vy vz bx by bz P C',real=True)
v=s.Matrix([vx,vy,vz]); mag=s.Matrix([bx,by,bz]); gam=1/(1-v.dot(v)); W=2*P+C
E=-v.cross(mag); rho=W*gam-P+(mag.dot(mag)+E.dot(E))/2
j=W*gam*v+E.cross(mag)
at={vx:0,vy:0,vz:u,bx:0,by:0,bz:b,P:(w-C)/2}
eq('parallel density derivative p',s.diff(rho,P).subs(at),J[0,0])
eq('parallel density derivative v',s.diff(rho,vz).subs(at),J[0,1])
eq('parallel momentum derivative p',s.diff(j[2],P).subs(at),J[1,0])
eq('parallel momentum derivative v',s.diff(j[2],vz).subs(at),J[1,1])
eq('density magnetic derivative',s.diff(rho,bz).subs(at),b)
for i in (0,1):
    eq('transverse velocity coefficient',s.diff(j[i],v[i]).subs(at),w*G2+b*b)
    eq('transverse magnetic coefficient',s.diff(j[i],mag[i]).subs(at),-u*b)
eq('full primitive Jacobian determinant',s.Matrix([rho,*j]).jacobian([P,vx,vy,vz]).subs(at).det(),w*G2*(w*G2+b*b)**2)
print(f'{len(checks)}/{len(checks)} exact assertions PASS; SymPy {s.__version__}')
