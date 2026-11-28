"""Exact finite checks; not a PDE trajectory, Selmer computation or kernel receipt."""
import sympy as S
from fractions import Fraction as Q
from itertools import product

# NS: physical periodic same-output cell countercontrol, all ordered incidences.
k=S.Matrix([4,0,0]); P=S.eye(3)-k*k.T/k.dot(k)
U={(2,1,0):S.Matrix([1,-2,0]),(2,-1,0):S.Matrix([0,0,1]),
   (2,6,0):S.Matrix([1,-S.Rational(1,3),0]),(2,-6,0):S.Matrix([0,0,-2])}
U.update({tuple(-v for v in p):u.conjugate() for p,u in list(U.items())})
rows=[]
for p,u in U.items():
    assert S.Matrix(p).dot(u)==0
    q=tuple(int(x-y) for x,y in zip(k,p))
    if q not in U: continue
    N=P*(S.I*k.dot(u)*U[q]); r=sum(x*x for x in p+q)
    rows.append((p,q,N,r))
assert len(rows)==4 and sum(N!=S.zeros(3,1) for p,q,N,r in rows)==2
a=k.dot(k); J=0; count=0
for (_,_,N,r),(_,_,M,t) in product(rows,repeat=2):
    lam=r+t;s=lam-a; assert s>=0
    G=2*S.re(N.dot(M.conjugate()))
    J+=s*G/(a*lam**2); count+=1
assert J<0
print('NS ordered source pairs',count,'signed time-endpoint coefficient',J)
# Scalar time transport, arbitrary symbolic forcing integral kernel.
a,l,h=S.symbols('a l h',positive=True)
s=S.symbols('s',nonnegative=True); tau=S.symbols('tau',real=True)
K=s/(a*(a+s))
assert S.simplify(S.integrate(K*S.exp(-(a+s)*tau),(tau,0,h))-K*(1-S.exp(-(a+s)*h))/(a+s))==0
print('NS exact time kernel: 1 identity')

# BSD: exact number field points, unit class representative and doubling.
z=S.sqrt(5); eps=(1+z)/2
x=2-z;y=4-2*z
assert S.simplify(y*y-x*x*x+x)==0
assert S.simplify(x+eps**(-3))==0
assert S.simplify(eps*(1-z)/2)==-1
assert 4**2==2**3+4*2
slope=(3*x*x-1)/(2*y)
x2=S.simplify(slope*slope-2*x);y2=S.simplify(slope*(x-x2)-y)
assert x2==S.Rational(5,4) and y2*y2==S.Rational(9,64)*5
print('BSD 6 exact field/curve identities; double',x2,y2)
# Class signs under real embeddings; E' positive classes only 1,2.
classes=[]
for sign,b,c in product((-1,1),range(2),range(2)):
    signs=(sign,sign*(-1)**b)
    if signs==(1,1):classes.append((sign,b,c))
assert classes==[(1,0,0),(1,0,1)]
print('BSD 8 real sign class fixtures')

# Hodge: exact trace-form determinant norm on actual cubic/quintic fields.
x=S.symbols('x')
count=0
for f in [x**3+x*x-2*x-1,x**3-3*x+1,x**5+x**4-4*x**3-3*x*x+3*x+1]:
    d=S.degree(f,x); A=S.zeros(d)
    for j in range(d-1):A[j+1,j]=1
    for j in range(d):A[j,d-1]=-f.coeff(x,j)
    for m in [3,4,6]:
        for b in [S.eye(d),2*S.eye(d)+A, A*A+S.eye(d)]:
            G=S.Matrix(d,d,lambda i,j:S.trace(b*A**(i+j))/S.factorial(m))
            assert S.simplify(G.det()-S.discriminant(f,x)*b.det()/S.factorial(m)**d)==0
            count+=1
    # Field-linear isometry with sign -1 on an abstract relative space.
    m=3; U=S.diag(-1,1,1); Qm=S.diag(1,1,-1)
    assert U.T*Qm*U==Qm and U.det()==-1
print('Hodge trace determinant identities',count,'3 reflection checks')

# RH: actual quadratic field O_K=Z[epsilon], split/inert/ramified Euler factors.
count=0
for p in list(S.primerange(2,300)):
    roots=sum((t*t-t-1)%p==0 for t in range(p))
    chi=0 if p==5 else (1 if p%5 in (1,4) else -1)
    assert roots==1+chi
    for j in range(7):
        ideal_count= j+1 if roots==2 else (1 if roots==1 or j%2==0 else 0)
        assert ideal_count==sum(chi**i for i in range(j+1))
        count+=1
print('RH quadratic Euler coefficients:',count,'including ramified prime 5')
