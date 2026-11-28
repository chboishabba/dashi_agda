"""Explicit full-rank CM period seed for the reported cubic RM quadratic form.
Exact field, finite-field and perturbation bounds; not a period-map computation.
"""
from fractions import Fraction as Q
import sympy as s

checks=0
def ck(x):
    global checks
    if not x: raise AssertionError('cubic CM period guard failed')
    checks+=1

t,x=s.symbols('t x')
f=s.Poly(t**3+t**2-2*t-1,t,domain=s.QQ)
ck(f.is_irreducible and f.discriminant()==49)
pi=2-t
# theta is a unit, pi has norm 7. Qdiag determinant theta^2*pi^3.
ck(s.resultant(f.as_expr(),t,t)==1)
ck(s.resultant(f.as_expr(),pi,t)==7)
q=[t,t*pi,-1,-pi,-1,-pi]
ck(s.expand(s.prod(q)-t**2*pi**3)==0)
# Isolate the three real embeddings using exact sign changes.
intervals=[(Q(-19,10),Q(-17,10)),(Q(-1,2),Q(-2,5)),(Q(6,5),Q(13,10))]
for a,b in intervals:
    ck(f.eval(a)*f.eval(b)<0)
    ck(min(abs(a),abs(b))>=Q(2,5))
    ck(2-b>=Q(7,10))
    ck(min(abs(a),abs(b))*(2-b)>=Q(1,3))
ck(sum(a>0 for a,b in intervals)==1)
E=s.Matrix([[0,-1,-4,0,4,-6],[1,0,-5,2,-5,-1],[4,5,0,3,-6,2],[0,-2,-3,0,-3,-6],[-4,5,6,3,0,-5],[6,1,-2,6,5,0]])
ck(E.T==-E)
D=130001
ck(D%13==1)
rowmax=max(sum(abs(x) for x in E.row(i)) for i in range(6))
ck(rowmax<=30)
# In coordinates scaled by |Qdiag|^(1/2), the base operator is
# a normal skew matrix, eigenvalues +/- i*k*sqrt(pi), k=1,2,3.
# The perturbation norm is bounded by rowmax / (D*min |q_i|).
ck(Q(3*rowmax,D)<Q(1,1000))
ck(Q(7,10)>Q(1,2)**2)
ck(Q(2,1000)<Q(1,2))
# Exact irreducible polynomial reduction at the prime theta=7 mod 13.
p=13;th=7; pp=(2-th)%p
ck(f.eval(th)%p==0)
ck(f.diff().eval(th)%p!=0)
Qdiag=s.diag(*[int(s.sympify(a).subs(t,th))%p for a in q])
ck(int(Qdiag.det())%p!=0)
S0=s.zeros(6)
for i,u in enumerate([th,-1,-1]):
    S0[2*i,2*i+1]=-(i+1)*u*pp
    S0[2*i+1,2*i]=-S0[2*i,2*i+1]
A=(s.diag(*(pow(int(Qdiag[i,i]),-1,p) for i in range(6)))*(S0+E)).applyfunc(lambda v:int(v)%p)
ck((A.T*Qdiag+Qdiag*A).applyfunc(lambda v:int(v)%p)==s.zeros(6))
g=s.Poly(A.charpoly(x).as_expr(),x,modulus=p)
ck(g==s.Poly(x**6-2*x**4-2*x**2+6,x,modulus=p))
ck(g.is_irreducible)
# Rabin finite field irreducibility, independent of factor() result.
def xpowmod(n):
    r=s.Poly(1,x,modulus=p); b=s.Poly(x,x,modulus=p)
    while n:
        if n&1:r=(r*b).rem(g)
        b=(b*b).rem(g);n//=2
    return r
xp=s.Poly(x,x,modulus=p)
ck(xpowmod(p**6)==xp)
for d in (2,3):ck(s.gcd(xpowmod(p**d)-xp,g).degree()==0)
print(f'{checks}/{checks} exact CM seed guards PASS')
print('mod 13 irreducible characteristic polynomial:',g.as_expr())
print('row norm bound:',rowmax,'perturbation <',Q(3*rowmax,D))
