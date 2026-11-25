"""Exact algebra for curved curl/Hodge and stress work; no PDE execution."""
import sympy as s
checks=0
def eq(a,b):
    global checks
    d=a-b
    assert all(s.simplify(x)==0 for x in (list(d) if isinstance(d,s.MatrixBase) else [d]))
    checks+=1
# Actual non-diagonal positive metric via a triangular frame, det(frame)=1.
a,b,c,t=s.symbols('a b c t', real=True)
R=s.Matrix([[1,a,b],[0,1,c],[0,0,1]])
g=R.T*R; M=g.inv(); N=g
# Symmetric general metric variation, evaluated at this metric.
p,q,r,u,v,w=s.symbols('p q r u v w', real=True)
H=s.Matrix([[p,u,v],[u,q,w],[v,w,r]])
tr=s.trace(M*H)
Md=tr*M/2-M*H*M
Nd=H-tr*g/2
eq(M*N,s.eye(3))
eq(Md*N+M*Nd,s.zeros(3))
D=s.Matrix(s.symbols('D:3')); B=s.Matrix(s.symbols('B:3'))
# At det(g)=1, E and B are the same contravariant vectors as flux densities.
S=(D.dot(g*D)+B.dot(g*B))*M/2-D*D.T-B*B.T
eq((D.dot(Nd*D)+B.dot(Nd*B))/2,-s.trace(S*H)/2)
# Curl metric variation C=M^-1 C_flat (formal coordinate operator symbol).
k=s.Matrix(s.symbols('k:3')); curl=s.Matrix([[0,-k[2],k[1]],[k[2],0,-k[0]],[-k[1],k[0],0]])
eq(Nd*curl,-N*Md*N*curl)
# General symmetric quadratic storage discrete chain rule.
K=s.Matrix([[p,u,v],[u,q,w],[v,w,r]])
L=s.Matrix([[a,b,c],[b,t,u],[c,u,v]])
x=s.Matrix(s.symbols('x:3')); y=s.Matrix(s.symbols('y:3'))
eq((y.dot(L*y)-x.dot(K*x))/2,((K+L)*(x+y)/4).dot(y-x)+(y.dot((L-K)*y)+x.dot((L-K)*x))/4)
# Ideal advection of a 1-form and 2-form: density of their wedge.
J=s.Matrix(3,3,s.symbols('j:9')); A=s.Matrix(s.symbols('A:3'))
eq((-J.T*A).dot(B)+A.dot(J*B-s.trace(J)*B),-s.trace(J)*A.dot(B))
# Original Hopf decay envelopes at unit scale.
rho=s.symbols('rho',nonnegative=True)
eq(s.integrate(rho**2/(1+rho**2)**3,(rho,0,s.oo)),s.pi/16)
print(f'{checks}/{checks} exact assertions PASS; SymPy {s.__version__}')
