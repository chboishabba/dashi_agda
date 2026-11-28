"""Exact finite controls for NS A/B horizon and signed helicity geometry.
Not a PDE solve, native kernel run, or all-data regularity claim.
"""
from fractions import Fraction as Q
from itertools import product
import sympy as s

checks = 0
def ck(ok):
    global checks
    if not ok:
        raise AssertionError('NS A/B finite-horizon guard failed')
    checks += 1

# The cubic lattice shell contains 24n^2+2 points, not a sphere count.
for n in range(1, 9):
    N = sum(max(abs(x),abs(y),abs(z)) == n for x,y,z in product(range(-n,n+1),repeat=3))
    ck(N == 24*n*n+2)
    ck(Q(N,n*n) <= 26)
    ck(Q(N,n**4) <= Q(26,n*n))
for N in range(1, 65):
    ck(sum(Q(24*n*n+2,n*n) for n in range(1,N+1)) <= 26*N)
    ck(sum(Q(24*n*n+2,n**4) for n in range(N+1,2*N+1)) <= Q(26,N)-Q(26,2*N))
    ck(Q(1,(N+1)**2) <= Q(1,N)-Q(1,N+1))
# r=sqrt(D/E), N=floor(r), t=r/N in [1,2].  t+1/t+2<=9/2.
for k in range(101):
    t=1+Q(k,100)
    ck(t+1/t+2 <= Q(9,2))
ck(26*Q(9,2)==117)
ck(117**2 == 13689 and 13689 < 11**4)
ck(256*Q(22,7)**2 < 8**4)
# Exact radial integral of each Cauchy weight on a truncated interval.
r,R,S=s.symbols('r R S', positive=True)
ck(s.integrate(4*s.pi,(r,0,R))==4*s.pi*R)
ck(s.simplify(s.integrate(4*s.pi/r**2,(r,R,S))-4*s.pi*(1/R-1/S))==0)
ck(s.integrate(4*s.pi/r**2,(r,R,s.oo))==4*s.pi/R)
# Time selection constants and strict threshold, no division by E0 needed.
nu,T,E,K,L=s.symbols('nu T E K L', positive=True)
ck(s.expand(2*nu*T*(2*nu)**4-32*nu**5*T)==0)
ck(Q(8**4,32)==128)
ck(Q(11**4,32)==Q(14641,32))
# Signed balance: total dissipative helicity is not |signed helicity|.
for a,b in product(range(-4,5),repeat=2):
    ck(a+b==abs(a-b)+2*min(a,b))
# Actual positive-helicity Fourier inputs at different radii.
# p=(1,0,0), q=(0,2,0), a=(0,1,i), b=(i,0,1).
p=s.Matrix([1,0,0]); q=s.Matrix([0,2,0]); k=p+q
I=s.I; a=s.Matrix([0,1,I]); b=s.Matrix([I,0,1])
ck(p.dot(a)==0 and q.dot(b)==0)
ck(I*p.cross(a)==a and I*q.cross(b)==2*b)
P=s.eye(3)-k*k.T/k.dot(k)
# Paired exact Leray RHS (velocity equation with negative advection).
N=s.simplify(-I*P*(a.dot(q)*b+b.dot(p)*a))
ck(k.dot(N)==0)
C=I*s.Matrix([[0,-k[2],k[1]],[k[2],0,-k[0]],[-k[1],k[0],0]])
Pminus=(P-C/s.sqrt(5))/2
minor=s.simplify(Pminus*N)
ck(s.simplify(C*minor+s.sqrt(5)*minor)==s.zeros(3,1))
ck(minor!=s.zeros(3,1))
minor2=s.simplify((s.conjugate(minor).T*minor)[0])
ck(s.simplify(minor2-(Q(7,5)-3*s.sqrt(5)/5))==0)
ck(minor2.is_positive is True)
print(f'{checks}/{checks} exact A/B controls PASS')
print('opposite helicity creation, norm squared:',minor2)
