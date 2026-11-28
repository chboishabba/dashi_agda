#!/usr/bin/env python3
"""Original Hopf induction on native nonperiodic cube; selected driven SG model."""
import sympy as s
from itertools import product, combinations
checks=[]
def ck(name, p):
    assert p, name
    checks.append(name)
def eq(name,a,b):
    d=a-b
    ck(name, all(s.simplify(v)==0 for v in d) if isinstance(d,s.MatrixBase) else s.simplify(d)==0)
x,y,z,t=s.symbols('x y z t',real=True); X=(x,y,z); D=1+x*x+y*y+z*z
A=2*s.Matrix([2*x*z-2*y,2*x+2*y*z,1-x*x-y*y+z*z])/D**2
B=4*A/D
curl=lambda v:s.Matrix([s.diff(v[2],y)-s.diff(v[1],z),s.diff(v[0],z)-s.diff(v[2],x),s.diff(v[1],x)-s.diff(v[0],y)])
div=lambda v:sum(s.diff(v[i],X[i]) for i in range(3))
a=s.Function('a')(t); Bt=a*B; E=-s.diff(a,t)*A
rho=div(E); J=curl(Bt)-E.diff(t)
eq('original curl',curl(A),B)
eq('Faraday',curl(E)+Bt.diff(t),s.zeros(3,1))
eq('magnetic divergence',div(Bt),0)
eq('external continuity',rho.diff(t)+div(J),0)
# Exact line integration primitives for every native bond.
u,c=s.symbols('u c',real=True,positive=True)
I1=s.atan(u/s.sqrt(c))/s.sqrt(c)
I2=u/(2*c*(c+u*u))+s.atan(u/s.sqrt(c))/(2*c**s.Rational(3,2))
U,V=s.symbols('U V',real=True)
eq('linear numerator primitive',s.diff(-U/(2*(c+u*u))+V*I2,u),(U*u+V)/(c+u*u)**2)
eq('quadratic axial primitive',s.diff(2*I1+4*(1-c)*I2,u),2*(2-c+u*u)/(c+u*u)**2)
# Native positive bonds x/y/z, segment lower/upper, other coordinates in -1,0,1.
pts=list(product((-1,0,1),repeat=3)); edges=[]
for axis in range(3):
    for lo in (-1,0):
        for others in product((-1,0,1),repeat=2):
            p=list(others);p.insert(axis,lo);q=p.copy();q[axis]+=1;edges.append((tuple(p),tuple(q)))
G=s.zeros(27,54)
for i,(p,q) in enumerate(edges):G[pts.index(p),i]=-1;G[pts.index(q),i]=1
faces=[]
for i,j in combinations(range(3),2):
    for a0,b0,k in product((-1,0),(-1,0),(-1,0,1)):
        p=[k]*3;p[i]=a0;p[j]=b0;v=p.copy();v[i]+=1;w=p.copy();w[j]+=1;r=v.copy();r[j]+=1
        row=s.zeros(1,54)
        for a1,b1,sgn in [(p,v,1),(v,r,1),(w,r,-1),(p,w,-1)]:row[edges.index((tuple(a1),tuple(b1)))]=sgn
        faces.append(row)
C=s.Matrix.vstack(*faces)
ck('native counts',len(pts)==27 and len(edges)==54 and C.rows==36)
eq('all face boundaries close',C*G.T,s.zeros(36,27))
ck('connected graph rank',G.rank()==26)
ck('face rank',C.rank()==28)
# Original xy perimeter in z=0 (8 native bonds), counterclockwise.
ring=[(-1,-1,0),(0,-1,0),(1,-1,0),(1,0,0),(1,1,0),(0,1,0),(-1,1,0),(-1,0,0)]
cycle=s.zeros(54,1);ell=s.Rational(1,3)+s.atan(1/s.sqrt(2))/s.sqrt(2)
for p,q in zip(ring,ring[1:]+ring[:1]):
    axis=next(i for i in range(3) if p[i]!=q[i]);sgn=q[axis]-p[axis];e=(p,q) if sgn==1 else (q,p);cycle[edges.index(e)]=sgn
    expr=A[axis].subs({X[i]:p[i] for i in range(3) if i!=axis})*sgn
    eq('original oriented ring integrand',expr,4/(2+X[axis]**2)**2)
    eq('original exact ring voltage coefficient',4*(I2.subs({c:2,u:1})-I2.subs({c:2,u:0})),ell)
eq('ring divergence zero',G*cycle,s.zeros(27,1))
# Sum four elementary xy faces in z=0 is the ring; face order is (axis pair, a0,b0,k).
face_sum=sum((C.row(i) for i in range(12) if i%3==1),s.zeros(1,54))
eq('ring is original four-face boundary',face_sum.T,cycle)
# SG convention: xi is electrical work / RT along oriented bond.
xi=s.symbols('xi',real=True,nonzero=True); bern=lambda v:v/(s.exp(v)-1)
eq('SG drift difference',bern(-xi)-bern(xi),xi)
eq('SG detailed balance ratio',bern(-xi),s.exp(xi)*bern(xi))
eq('SG zero drift limit',s.limit(bern(xi),xi,0),1)
kappa,n,RT=s.symbols('kappa n RT',positive=True)
# Same uniform concentration, opposite unit charges, opposite oriented molar flux.
Fplus=kappa*n*(bern(-xi)-bern(xi)); Fminus=kappa*n*(bern(xi)-bern(-xi))
eq('positive flux',Fplus,kappa*n*xi)
eq('negative flux',Fminus,-kappa*n*xi)
eq('zero total molar flow',Fplus+Fminus,0)
eq('nonzero signed current coefficient',Fplus-Fminus,2*kappa*n*xi)
eq('uniform two-ion inventories stationary',G*(cycle*kappa*n*xi),s.zeros(27,1))
eq('ring power',8*RT*xi*(Fplus-Fminus),16*RT*kappa*n*xi**2)
# Nonzero xi ensures positive power; reversal keeps power, reverses current.
ck('strict positive work', (16*RT*kappa*n*xi**2).is_positive)
eq('reverse current',(Fplus-Fminus).subs(xi,-xi),-(Fplus-Fminus))
eq('reverse work',(16*RT*kappa*n*xi**2).subs(xi,-xi),16*RT*kappa*n*xi**2)
# Gauge: edge potential differences annihilate every cycle; independent vertex zero mode.
phi=s.Matrix(s.symbols('p:27'));eq('constant gauge mode',G.T*s.ones(27,1),s.zeros(54,1))
eq('all face gradient circulation',C*G.T*phi,s.zeros(36,1))
eq('ring gradient work zero',(cycle.T*G.T*phi)[0],0)
print(f'{len(checks)}/{len(checks)} exact checks PASS; SymPy {s.__version__}')
