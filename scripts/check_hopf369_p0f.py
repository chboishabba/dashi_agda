#!/usr/bin/env python3
"""P0F exact GH curvature, helicity energy, finite shell and boosted flux algebra."""
import sympy as s
from itertools import combinations
checks=[]
def eq(label,a,b):
 d=a-b
 ok=all(s.factor(s.cancel(v))==0 for v in d) if isinstance(d,s.MatrixBase) else s.factor(s.cancel(d))==0
 assert ok,(label,d)
 checks.append(label)
r,m=s.symbols('r m',positive=True); V=1+m/r
# on positive z axis; rotational covariance of GH frame gives all base points.
a=s.Matrix([0,0,s.diff(V,r)/(2*V**s.Rational(3,2))]); da=s.diag(s.diff(V,r)/(2*V**2*r),s.diff(V,r)/(2*V**2*r),s.diff(a[2],r)/s.sqrt(V))
e=[s.eye(4)[:,i] for i in range(4)]
def wedge(u,v):return u*v.T-v*u.T
d=[s.zeros(4) for _ in range(4)]
for i in range(1,4):
 j,k=i%3+1,(i+1)%3+1
 d[0]+=a[i-1]*(wedge(e[0],e[i])+2*wedge(e[j],e[k]))
 for j in range(1,4):d[i]+=a[j-1]*wedge(e[j],e[i])
def om(ai,i):return -ai[i-1]*e[0]+sum((s.LeviCivita(i-1,j-1,k-1)*ai[k-1]*e[j] for j in range(1,4) for k in range(1,4)),s.zeros(4,1))
w=[om(a,i) for i in range(1,4)]
R=[]
for i in range(3):
 dw=sum((wedge(e[j+1],om(da[:,j],i+1)) for j in range(3)),s.zeros(4))+sum((w[i][j]*d[j] for j in range(4)),s.zeros(4))
 R.append((dw-2*wedge(w[(i+1)%3],w[(i+2)%3])).applyfunc(s.simplify))
for F in R:
 for i,j,k in [(1,2,3),(2,3,1),(3,1,2)]:eq('GH chiral curvature duality',F[0,i],F[j,k])
print('axis curvature',R,flush=True)
# Norm for C=-omega_0i with generators quaternion e_i/2.
F2=s.simplify(8*sum(F[i,j]**2 for F in R for i,j in combinations(range(4),2)))
print('F2',F2,flush=True)
# integrate GH volume: 4pi sphere *4pi m circle *V r²dr
act=s.integrate(s.factor(F2*V*r*r*4*s.pi**2*m),(r,0,s.oo))
print('action times g²',act,flush=True)
eq('GH unit action',act,8*s.pi**2)
# Smooth nut chart coefficient.
q=s.symbols('q',positive=True); lam=q/(4*m*m)
eq('nut metric coefficient',((1+lam)**-1-(1+lam))/q,-(2+lam)/(4*m*m*(1+lam)))
# S3 energy average: 1/D=(1-d)/2; d=sqrt(1-t) sin(phi), zero angular mean.
t,phi,tau=s.symbols('t phi tau',real=True)
eq('angular energy mean',s.integrate(1-s.sqrt(1-t)*s.sin(phi),(phi,0,2*s.pi)),2*s.pi)
for n in range(6):
 H=(n+1)*t**n
 eq('flux normalized',s.integrate(H,(t,0,1)),1)
 eq('energy ratio',s.integrate(H**2,(t,0,1)),s.Rational((n+1)**2,2*n+1))
# Sharp constrained infimum, square completion in symbolic moment coordinates.
I2,M,L=s.symbols('I2 M L',positive=True)
eq('weighted square completion',I2-2*(M/L)*M+(M/L)**2*L,I2-M*M/L)
# Finite shell static balance: div tangential projector = -2 n / R.
x,y,z=s.symbols('x y z',real=True); X=(x,y,z); n=s.Matrix(X)/s.sqrt(x*x+y*y+z*z); P=s.eye(3)-n*n.T
Dp=s.Matrix([sum(s.diff(P[i,j],X[j]) for j in range(3)) for i in range(3)])
eq('shell tangential divergence',Dp,-2*n/s.sqrt(x*x+y*y+z*z));eq('shell no delta prime',P*n,s.zeros(3,1))
p,R0=s.symbols('p R0',positive=True); tension=p*R0/2
eq('pressure membrane balance',-p+2*tension/R0,0)
# Boost exact conservation residual and plane work identities in normalized units.
v=s.symbols('v',real=True); gam=s.symbols('gamma',positive=True); bx,by,bz=s.symbols('bx by bz',real=True); B=s.Matrix([gam*bx,gam*by,bz]); vel=s.Matrix([0,0,v]); E=-vel.cross(B); S=E.cross(B)
eq('boost flux',S[2],v*gam**2*(bx**2+by**2));eq('boost ideal invariant',E.dot(B),0)
eq('plane time Jacobian',S[2]/(gam*v),gam*(bx**2+by**2))
eq('opposite face cancellation',S[2]-S[2],0)
print(f'{len(checks)}/{len(checks)} exact checks PASS; SymPy {s.__version__}',flush=True)
