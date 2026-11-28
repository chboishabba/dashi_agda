"""P0V: exact algebra for analytic majorant, asymptotic split and KK jets."""
import sympy as s
checks=[]
def eq(name,a,b):
    d=a-b
    assert all(s.simplify(v)==0 for v in (list(d) if isinstance(d,s.MatrixBase) else [d])),name
    checks.append(name)
rho,eta,c,n=s.symbols('rho eta c n',positive=True)
z,w,t=s.symbols('z w t',real=True)
P=(1-z/rho)*w-n*(3/rho+1/eta)*w*w/2-c*t
wt=-s.diff(P,t)/s.diff(P,w); wz=-s.diff(P,z)/s.diff(P,w)
eq('scalar CK implicit majorant PDE',wt*(1-z/rho-n*w/eta),c*(1+3*n*wz))
x,y,z=s.symbols('x y z',real=True); X=(x,y,z); D=1+x*x+y*y+z*z
A=2*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**2
curl=lambda a:s.Matrix([s.diff(a[2],y)-s.diff(a[1],z),s.diff(a[0],z)-s.diff(a[2],x),s.diff(a[1],x)-s.diff(a[0],y)])
B=curl(A); J=curl(B)
eq('original curl',B,4*A/D)
eq('magnetic helicity density',A.dot(B),16/D**3)
eq('current helicity density',B.dot(J),256/D**5)
r=s.symbols('r',nonnegative=True)
eq('current helicity integral',4*s.pi*s.integrate(256*r*r/(1+r*r)**5,(r,0,s.oo)),20*s.pi**2)
eq('radial KK Newton bound',s.integrate(64*r/(1+r*r)**4,(r,0,s.oo))/12,s.Rational(8,9))
# Mixed Ricci of unit-radius seed, in its horizontal frame.
f,g,h=[s.Function(k)(*X) for k in ('f','g','h')]
F=s.Matrix([[0,f,g],[-f,0,h],[-g,-h,0]])
Z=range(4)
structure=lambda i,j,k:-F[i,j] if i<3 and j<3 and k==3 else 0
G=lambda i,j,k:(structure(i,j,k)-structure(j,k,i)+structure(k,i,j))/2
der=lambda i,a:s.diff(a,X[i]) if i<3 else 0
def R(i,j,k,l):
    return der(i,G(j,k,l))-der(j,G(i,k,l))+sum(G(j,k,m)*G(i,m,l)-G(i,k,m)*G(j,m,l)-structure(i,j,m)*G(m,k,l) for m in Z)
for i in range(3):
    eq('mixed seed Ricci',sum(R(j,i,3,j) for j in Z),sum(s.diff(F[i,j],X[j]) for j in range(3))/2)
    for j in range(3):
        eq('horizontal seed Ricci',sum(R(k,i,j,k) for k in Z),-sum(F[i,k]*F[j,k] for k in range(3))/2)
p=s.Function('p')(*X); eps=s.symbols('eps',positive=True)
F0=s.Matrix(3,3,lambda i,j:eps*(s.diff(A[j],X[i])-s.diff(A[i],X[j])))
Fdotdot=s.Matrix([sum(s.diff(p*p*F0[j,i],X[j]) for j in range(3))/p**4 for i in range(3)])
grad=s.Matrix([s.diff(p,q) for q in X])
eq('KK Maxwell acceleration',Fdotdot,-eps*(J/p**2+2*grad.cross(B)/p**3))
eq('KK signed helicity second derivative density',2*eps*B.dot(Fdotdot),-2*eps**2*B.dot(J)/p**2)
# Full metric recovery from block matrix, with independent radius and connection.
a=s.Matrix(s.symbols('a:3')); q=s.symbols('q',positive=True)
u,v,w=s.symbols('u v w',positive=True); H=s.diag(u,v,w)
metric=(H+q*a*a.T).row_join(q*a).col_join((q*a.T).row_join(s.Matrix([[q]])))
eq('vertical radius recovery',metric[3,3],q)
eq('mixed connection recovery',metric[:3,3]/q,a)
eq('horizontal Schur recovery',metric[:3,:3]-metric[:3,3]*metric[3,:3]/q,H)
# Initial tail scale retains 1/r coefficient rather than declaring L2.
m,l=s.symbols('m l',real=True)
eq('G4 dilation coefficient',s.diff((1+2*m*l)**2,l).subs(l,0),s.diff((1+m*l)**4,l).subs(l,0))
eq('G3 dilation coefficient',s.diff((1+m*l)**2,l).subs(l,0),2*m)
eq('weighted remainder L2 integral',s.integrate(r*r/(1+r*r)**2,(r,0,s.oo)),s.pi/4)
print(f'{len(checks)}/{len(checks)} exact assertions PASS; SymPy {s.__version__}')
