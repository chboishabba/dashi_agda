"""Finite exact controls for four classical geometric reductions, not Clay proofs."""
from fractions import Fraction as Q
from itertools import product, permutations
from math import comb, gcd
import sympy as s
checks={k:0 for k in ('BSD','RH','NS','Hodge')}
def ck(lane,ok):
    if not ok: raise AssertionError(lane)
    checks[lane]+=1
X=s.Symbol('X')
# Actual previous level-one residues; integral polynomial lifts are fixtures,
# not the original infinite unit series or new cusp evaluations.
for p,ds in ((5,[1]*5),(11,[4,7,0,7,7,7,7,0,7,4,5])):
    f=s.Poly(sum(a*X**j for j,a in enumerate(ds)),X,modulus=p)
    u,r=divmod(f,s.Poly((X-1)**4,X,modulus=p))
    ck('BSD',r.is_zero and u.eval(1)%p!=0)
    U=[int(u.nth(j)) for j in range(p)]; aug=sum(U)
    V=[Q(a)-Q(aug,p) for a in U]
    ck('BSD',sum(V)==0)
    ck('BSD',all(v.denominator==p for v in V))
    for j in range(p):
        d=sum((-1)**(4-i)*comb(4,i)*V[(j-i)%p] for i in range(5))
        ck('BSD',d.denominator==1 and d.numerator%p==ds[j])
        ck('BSD',V[j]-V[0]==U[j]-U[0])
    ck('BSD',(-p*V[0])%p==aug%p)
    for n in range(1,5):
        q=p**n; roots={pow(a,p**(n-1),q) for a in range(1,p)}
        ck('BSD',len(roots)==p-1)
        ck('BSD',all(pow(a,p-1,q)==1 for a in roots))
        ck('BSD',all(a*b%q in roots for a in roots for b in roots))
        ck('BSD',len({a*pow(1+p,j,q)%q for a in roots for j in range(p**(n-1))})==q-q//p)
# Polynomial interpolation and exact reflected pair sign on HYPOTHETICAL zeros.
z=s.Symbol('z'); I=s.I
for a in (s.Rational(1,7),s.Rational(2,5)):
    gam=s.Integer(17); zp=a+I*gam; zm=-a+I*gam
    other=[I*gam,I*(gam+1),s.Rational(1,3)+I*(gam-1),-s.Rational(1,3)+I*(gam-1),s.Rational(1,2),-s.Rational(1,2)]
    B=s.prod(z-w for w in other)
    P=B*((z-zm)/(zp-zm)/B.subs(z,zp)-(z-zp)/(zm-zp)/B.subs(z,zm))
    ck('RH',s.simplify(P.subs(z,zp))==1 and s.simplify(P.subs(z,zm))==-1)
    ck('RH',all(s.simplify(P.subs(z,w))==0 for w in other))
    ck('RH',s.simplify(P.subs(z,zp)*s.conjugate(P.subs(z,zm))+P.subs(z,zm)*s.conjugate(P.subs(z,zp)))==-2)
# Real divergence-free periodic Fourier field; exact complex integer coefficients.
# Verify the advector integration-by-parts identity on its actual triads.
def neg(k):return tuple(-a for a in k)
def dot(a,b):return sum(x*y for x,y in zip(a,b))
vel={}
for j,k in enumerate(((1,0,0),(0,1,0),(1,1,0),(0,0,1),(1,1,1),(1,0,1))):
    a=s.Matrix(k).cross(s.Matrix([j+1,2*j-3,1-j]));b=s.Matrix(k).cross(s.Matrix([1,3-j,2+j]))
    v=tuple(a[i]+I*b[i] for i in range(3));vel[k]=v;vel[neg(k)]=tuple(s.conjugate(x) for x in v)
for k,v in vel.items():ck('NS',s.expand(dot(k,v))==0)
for R2 in (1,2,3):
    lhs=rhs=transport=0
    for k,v in vel.items():
        if dot(k,k)>R2:continue
        for l,u in vel.items():
            r=neg(tuple(a+b for a,b in zip(k,l)))
            if r not in vel:continue
            w=vel[r]; b=I*dot(v,l)*dot(u,w)
            lhs+=b*dot(r,r)
            rhs+=-I*dot(k,r)*dot(v,l)*dot(u,w)
            transport+=-b*dot(l,r)
    ck('NS',s.expand(lhs-rhs)==0)
    ck('NS',s.expand(transport)==0)
    print('NS squared cutoff',R2,'signed low work',s.expand(lhs))
# Relative determinant alternation: exact coefficient-space controls, not cycles.
A=s.Matrix([[1,0,0,0,0,1],[0,1,0,0,0,1],[0,0,1,0,0,1],[0,0,0,1,0,1],[0,0,0,0,1,1],[0,0,0,0,0,0]])
ck('Hodge',A.rank()==5 and A.det()==0)
ck('Hodge',A*s.Matrix([-1,-1,-1,-1,-1,1])==s.zeros(6,1))
B=s.eye(6);ck('Hodge',B.det()==1)
for j in range(5):
    C=B.copy();C.col_swap(j,j+1);ck('Hodge',C.det()==-1)
print(checks, 'total',sum(checks.values()),'PASS')
