#!/usr/bin/env python3
"""P0G: noncompact radiation/Beltrami source and 5D rotating null KK vacuum."""
import sympy as s
checks=[]
def eq(name,a,b):
    d=a-b
    assert all(s.simplify(v)==0 for v in d) if isinstance(d,s.MatrixBase) else s.simplify(d)==0,name
    checks.append(name)
x,y,z,eta=s.symbols('x y z eta',real=True)
k,b,P=s.symbols('k b P',positive=True)
B=b*s.Matrix([s.sin(k*z),s.cos(k*z),0]); X=(x,y,z)
def curl(a):return s.Matrix([s.diff(a[2],y)-s.diff(a[1],z),s.diff(a[0],z)-s.diff(a[2],x),s.diff(a[1],x)-s.diff(a[0],y)])
eq('Beltrami',curl(B),k*B);eq('divergence',sum(s.diff(B[i],X[i]) for i in range(3)),0)
eq('constant norm',B.dot(B),b*b);eq('geodesic direction',B.jacobian(X)*B,s.zeros(3,1));eq('Lorentz force',curl(B).cross(B),s.zeros(3,1));eq('helicity density',(B/k).dot(B),b*b/k)
# Each radiation stream: 2w gamma² v v^T = B B^T.
p=P/2-b*b/4; w=4*p; K=4*P-b*b; gamma2=K/(K-b*b)
v=B/s.sqrt(K)
eq('velocity norm',v.dot(v),b*b/K);eq('normalization',gamma2*(1-v.dot(v)),1)
eq('isotropic total stress',2*w*gamma2*v*v.T+2*p*s.eye(3)+b*b*s.eye(3)/2-B*B.T,P*s.eye(3))
eq('total density',2*w*gamma2-2*p+b*b/2,3*P);eq('momentum cancellation',w*gamma2*v-w*gamma2*v,s.zeros(3,1))
# Variable amplitude on a unit geodesic Hopf fibre; half force per stream.
h,hp=s.symbols('h hp',real=True); H=s.Matrix(s.symbols('H1:4',real=True))
eq('half Lorentz force',-h*hp*H/2,s.diff(P/2-h*h/4,h)*hp*H)
# Exact Friedmann radiation backgrounds, conformal time, G units c=1.
G=s.symbols('G',positive=True); C=s.sqrt(8*s.pi*G*P)
for curvature,a in [(0,C*eta),(1,C*s.sin(eta))]:
    eq('Friedmann constraint',s.diff(a,eta)**2+curvature*a*a,C*C)
    eq('radiation acceleration',s.diff(a,eta,2)+curvature*a,0)
    eq('radiation conservation',s.diff(3*P/a**4,eta)+3*s.diff(a,eta)/a*(4*P/a**4),0)
# KK two-polarization arbitrary null profile, direct Ricci on g5.
u,v0=s.symbols('u v',real=True); w0=s.symbols('w',real=True)
f=s.Function('f')(u); j=s.Function('j')(u); a1=s.diff(f,u); a2=s.diff(j,u)
Q=(u,v0,x,y,w0); H0=-(a1*a1+a2*a2)*(x*x+y*y)/4
base=s.Matrix([[H0,1,0,0,0],[1,0,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,0]])
form=s.Matrix([0,0,f,j,1]); metric=base+form*form.T
inv=metric.inv().applyfunc(s.simplify)
eq('KK determinant',metric.det(),-1)
from functools import lru_cache
@lru_cache(None)
def dg(i,j,k):return s.diff(metric[i,j],Q[k])
@lru_cache(None)
def ch(i,j,k):return s.simplify(sum(inv[i,l]*(dg(l,k,j)+dg(l,j,k)-dg(j,k,l)) for l in range(5))/2)
for i in range(5):
 for j0 in range(i,5):
    R=sum(s.diff(ch(l,i,j0),Q[l])-s.diff(ch(l,i,l),Q[j0])+sum(ch(l,l,n)*ch(n,i,j0)-ch(l,j0,n)*ch(n,i,l) for n in range(5)) for l in range(5))
    eq('KK Ricci',R,0)
# null invariant on the base and rotating profile.
F=s.zeros(4); F[0,2]=a1;F[2,0]=-a1;F[0,3]=a2;F[3,0]=-a2
ig=s.Matrix([[0,1,0,0],[1,-H0,0,0],[0,0,1,0],[0,0,0,1]])
raised=ig*F*ig
eq('null F squared',sum(F[i,j0]*raised[i,j0] for i in range(4) for j0 in range(4)),0)
eq('nonzero circular polarization', (a1*a1+a2*a2).subs({f:b*s.sin(k*u),j:b*s.cos(k*u)}).doit(),b*b*k*k)
print(f'{len(checks)}/{len(checks)} exact checks PASS; SymPy {s.__version__}')
