"""Exact source-specific arithmetic/geometry regressions; not kernel proofs."""
from fractions import Fraction as Q
from itertools import product
import sympy as S

# A: projected divergence-free cells on the original common output.
k=S.Matrix([2,1,0]); k2=k.dot(k); P=S.eye(3)-k*k.T/k2
nu=S.Rational(3,2); a=nu*k2
rows=[]
for p in product(range(-1,3),repeat=3):
    p=S.Matrix(p); q=k-p
    if p.dot(p)==0 or q.dot(q)==0: continue
    u=p.cross(S.Matrix([1,2,3])); v=q.cross(S.Matrix([2,-1,1]))
    d=p-k/2; r=nu*(p.dot(p)+q.dot(q)); e=d.dot(d)
    N=P*(S.I*k.dot(u)*v); B2=u.dot(u)*v.dot(v)
    assert r==a/2+2*nu*e
    assert k.dot(u)==-2*d.dot(u)
    assert S.simplify(N.dot(N.conjugate()))<=4*e*B2
    rows.append((r,e,N,B2))
count=0
for (r,e,N,B2),(t,f,M,C2) in product(rows,repeat=2):
    s=2*nu*(e+f); K=s/(a*(a+s)); G=2*S.re(N.dot(M.conjugate()))
    assert r+t==a+s and K==1/a-1/(r+t)
    assert (K*G)**2 <= (8*(e+f)**2/(nu*k2**2))**2*B2*C2
    count+=1
print('NS:',len(rows),'physical cells;',count,'ordered pair fixtures')

# BSD: signed quadratic-extension eigenspaces, with ramified-prime negative control.
count=0
for ell,n in product((3,5,7),range(1,4)):
    m=ell**n; h=pow(2,-1,m)
    for x,y in product(range(min(m,9)),repeat=2):
        plus=h*(x+y)%m; minus=h*(x-y)%m
        assert (plus+minus)%m==x and (plus-minus)%m==y
        count+=1
assert S.Matrix([[1,1],[1,-1]]).det()==-2
x,y=Q(25,4),Q(75,8)
assert y*y==x**3-25*x
assert Q(45,64)==Q(5,4)**3-Q(5,4)
print('BSD:',count,'odd-prime projector fixtures; 3 additional identities')

# Hodge: exact dihedral cover character algebra, not a cycle proof.
z,t=S.symbols('z t')
for n in (7,9,11):
    phi=S.Poly(S.cyclotomic_poly(n,z),z,domain=S.QQ); deg=phi.degree()
    def red(p): return S.rem(S.Poly(p,z,domain=S.QQ),phi).as_expr()
    def mat(fn): return S.Matrix(deg,deg,lambda i,j:S.Poly(red(fn(j)),z).nth(i))
    R=mat(lambda j:z**(j+1)); J=mat(lambda j:z**((-j)%n)); I=S.eye(deg)
    assert R**n==I and J**2==I and J*R*J==R.inv()
    e=(I+J)/2; V=S.Matrix.hstack(*e.columnspace()); A=R+R.inv()
    assert e*e==e and e*A==A*e
    B=S.Matrix.hstack(*(V.gauss_jordan_solve(A*V[:,j])[0] for j in range(V.cols)))
    p=S.Poly(B.charpoly(t).as_expr(),t)
    expected={7:t**3+t**2-2*t-1,9:t**3-3*t+1,11:t**5+t**4-4*t**3-3*t**2+3*t+1}[n]
    assert p.as_expr()==expected and p.is_irreducible
    assert V.cols==deg//2 and V*B==A*V
    assert 2*e*R*V==A*V
    print('Hodge: conductor',n,'fixed sector degree',V.cols,'polynomial',p.as_expr())

# RH: outward exact rational log bounds and finite Robin boundary.
def log_bounds(x,N=32):
    assert x>=1
    z=(x-1)/(x+1)
    lo=2*sum(z**(2*j+1)/Q(2*j+1) for j in range(N))
    hi=lo+2*z**(2*N+1)/(Q(2*N+1)*(1-z*z))
    return lo,hi
l2,u2=log_bounds(Q(2))
g=sum(Q(1,j) for j in range(1,1025))-10*u2-Q(1,1024)
assert g>Q(576,1000)
e=sum(Q(576,1000)**j/Q(S.factorial(j)) for j in range(16))
L6000=12*l2+log_bounds(Q(375,256))[0]
Llog6000=3*l2+log_bounds(L6000/8)[0]
assert e*Llog6000>Q(403,105)
sig=[0]*6001
for d in range(1,6001):
    for n in range(d,6001,d): sig[n]+=d
assert max(Q(sig[n],n) for n in range(1,5041))==Q(403,105)
assert max(Q(sig[n],n) for n in range(5041,6001))==Q(171,49)
assert e*3*l2>Q(171,49) and 12*l2>8
print('RH: exact early maximum, 960 boundary integers, rational strict thresholds PASS')
