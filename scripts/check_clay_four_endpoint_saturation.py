import itertools as it
from collections import Counter
from fractions import Fraction
import sympy as s

counts = Counter()
def ck(group, value):
    if not value:
        raise RuntimeError(group)
    counts[group] += 1

# RH: exact coefficient formula for the pole-normalized residual.
z,a,h,x,L=s.symbols('z a h x L')
# exp(-L z) times [(a-z)(h-x) + sum_{j>=2} ((a-z)h)^j/j!]
for J in range(2,9):
    bracket=(a-z)*(h-x)+sum((a-z)**j*h**j/s.factorial(j) for j in range(2,J+1))
    direct=s.Poly(s.expand(bracket),z)
    for k in range(J+1):
        linear=(a*(h-x) if k==0 else -(h-x) if k==1 else 0)
        expected=linear+(-1)**k*sum(s.binomial(j,k)*a**(j-k)*h**j/s.factorial(j) for j in range(max(2,k),J+1))
        ck('RH',s.expand(direct.nth(k)-expected)==0)
    for m in range(5):
        fact=s.Poly(sum((-L*z)**j/s.factorial(j) for j in range(m+1)),z)
        conv=sum(direct.nth(k)*fact.nth(m-k) for k in range(m+1))
        ck('RH',s.expand((direct*fact).nth(m)-conv)==0)
# BSD: exact cyclotomic norm and Eisenstein ramification of the multiplier.
t=s.symbols('t')
for p in (3,5,7,11):
    for m in (1,2,3):
        q=p**m; d=s.totient(q)
        phi=s.Poly(s.cyclotomic_poly(q,t),t)
        ck('BSD',phi.eval(1)==p)
        ck('BSD',phi.resultant(s.Poly((t-1)**4,t))==p**4)
        shifted=s.Poly(s.cyclotomic_poly(q,t).subs(t,t+1),t)
        ck('BSD',shifted.degree()==d and shifted.LC()==1)
        ck('BSD',shifted.TC()==p)
        ck('BSD',all(c%p==0 for c in shifted.all_coeffs()[1:]))
        ck('BSD',Fraction(4,int(d))==Fraction(4,p**(m-1)*(p-1)))
# NS: exact Fourier stress for real divergence-free two-mode initial field.
p=(1,1,0); q=(0,1,0); ap=s.Matrix([1,-1,0]); aq=s.Matrix([1,0,0]); k=s.Matrix([1,0,0]); P=s.eye(3)-k*k.T
for lam in (s.Rational(1,64),s.Rational(1,8),s.Rational(1,2),s.Integer(1),s.Integer(3)):
    u={p:lam*ap/2,tuple(-i for i in p):lam*ap/2,q:lam*aq/2,tuple(-i for i in q):lam*aq/2}
    A={}
    for r,ur in u.items():
        rv=s.Matrix(r); ck('NS',rv.dot(ur)==0)
        for t,ut in u.items():
            tv=s.Matrix(t); m=tuple(i+j for i,j in zip(r,t)); A[m]=A.get(m,s.zeros(3))-ur.dot(ut)*rv*tv.T
    D=sum(s.Matrix(r).dot(s.Matrix(r))*ur.dot(ur) for r,ur in u.items())
    ck('NS',D==5*lam**2/2)
    total=0
    for m,B in A.items():
        mv=s.Matrix(m); d=mv.dot(mv)
        ck('NS',B==B.T)
        if d and d<=1:
            b=(s.eye(3)-mv*mv.T/d)*B*mv/d
            projected=mv*b.T+b*mv.T
            total+=s.trace(projected.T*projected)
    ck('NS',total==lam**4/4)
    ck('NS',s.simplify(total/D**3)==s.Rational(2,125)/lam**2)
# Hodge: exact A6 stabilizers fixing labelled retained coordinates.
perms=list(it.permutations(range(6)))
even=[p for p in perms if sum(p[i]>p[j] for i in range(6) for j in range(i+1,6))%2==0]
ck('Hodge',len(even)==360)
for r in range(7):
    for retained in it.combinations(range(6),r):
        fixed=[p for p in even if all(p[i]==i for i in retained)]
        n=6-r
        ck('Hodge',len(fixed)==(s.factorial(n)//2 if n>=2 else 1))
        if r==3:
            ck('Hodge',len(fixed)==3)
            ck('Hodge',all(tuple(p[p[p[i]]] for i in range(6))==tuple(range(6)) for p in fixed))
print(dict(counts),'TOTAL',sum(counts.values()))
