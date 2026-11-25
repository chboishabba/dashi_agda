from fractions import Fraction as Q
from itertools import product
from functools import lru_cache
import warnings
import sympy as s
from sympy.polys.numberfields import round_two
warnings.filterwarnings('ignore',category=s.utilities.exceptions.SymPyDeprecationWarning)
checks=0
def check(ok):
    global checks
    if not ok: raise AssertionError('exact check failed')
    checks+=1
x,a,b,c=s.symbols('x a b c'); f=s.Poly(x**3-66*x+289,x)
D=int(f.discriminant()); check(D==-1105083 and f.is_irreducible)
check(s.factorint(abs(D))=={3:4,7:1,1949:1})
check(s.expand(f.as_expr().subs(x,x-1))==x**3-3*x*x-63*x+354)
check(354%3==0 and 354%9!=0)
ZK,dK=round_two(f); check(dK==D)
# Minkowski bound (8/(9*pi))*sqrt(|D|) < 298; pi>3.14.
check(64*abs(D)*10000 < (298*9*314)**2)
@lru_cache(None)
def factors(p):
    check(s.isprime(p))
    fs=[(tuple(int(a)%p for a in g.all_coeffs()),int(e)) for g,e in s.factor_list(f,modulus=p)[1]]
    poly=s.Poly(1,x,modulus=p)
    for g,e in fs:
        q=s.Poly.from_list(g,x,modulus=p); check(q.is_irreducible); poly*=q**e
    check(poly==s.Poly(f,x,modulus=p))
    return fs
ideals=[(p,g) for p in s.primerange(2,298) for g,e in factors(int(p)) if p**(len(g)-1)<=297]
index={v:i for i,v in enumerate(ideals)}; check(len(index)==len(ideals)==75)
def norm(a,b,c):
    return a**3+132*a*a*c-66*a*b*b+867*a*b*c+4356*a*c*c-289*b**3+19074*b*c*c+83521*c**3
check(s.expand(s.resultant(f.as_expr(),a+b*x+c*x*x,x)-norm(a,b,c))==0)
def divides(g,a,b,c,p):
    coeff=[c%p,b%p,a%p]; d=len(g)-1
    for i in range(3-d):
        v=coeff[i]
        for j in range(d+1): coeff[i+j]=(coeff[i+j]-v*g[j])%p
    return all(v==0 for v in coeff)
cert=[(0,1,-1),(0,1,1),(1,-1,-1),(1,-1,1),(0,1,2),(0,2,-1),(0,2,1),(1,1,2),(1,2,-1),(2,-2,-1),(2,2,-1),(0,1,-3),(0,2,-3),(0,3,-1),(0,3,1),(1,-1,-3),(1,0,3),(1,3,-1),(2,-3,-1),(2,2,3),(2,3,-1),(3,-3,-2),(3,-3,1),(3,-2,0),(3,-1,-2),(3,-1,1),(3,1,1),(3,2,1),(3,3,-1),(0,1,-4),(0,1,4),(0,3,-4),(0,3,4),(0,4,-1),(0,4,1),(1,2,4),(1,4,-3),(2,4,1),(3,-1,4),(4,-3,0),(4,-3,1),(4,-1,-4),(4,-1,-3),(4,-1,2),(4,1,-2),(4,2,-1),(4,2,1),(4,3,-3),(4,4,-1),(0,5,-3),(0,5,2),(0,5,3),(1,0,5),(1,5,-2),(1,5,-1),(1,5,2),(2,5,-1),(3,5,-3),(4,3,5),(5,-4,-3),(5,-3,1),(5,-2,2),(5,-2,4),(5,-1,-3),(5,-1,3),(5,3,3),(0,6,-5),(1,4,-6),(2,6,5),(6,3,-1),(6,4,3),(0,3,-7),(0,7,-2),(0,17,-16)]
basis={}
for a,b,c in cert:
    n=abs(norm(a,b,c)); check(n>0); fs=s.factorint(n)
    check(s.prod(p**e for p,e in fs.items())==n)
    row=0
    for p,e in fs.items():
        p=int(p); e=int(e)
        hit=[g for g,_ in factors(p) if divides(g,a,b,c,p)]; check(len(hit)==1)
        g=hit[0]; d=len(g)-1; check(e%d==0)
        if (e//d)%2:
            check((p,g) in index); row^=1<<index[p,g]
    while row and row.bit_length()-1 in basis: row^=basis[row.bit_length()-1]
    check(row!=0); basis[row.bit_length()-1]=row
check(len(basis)==74)
# Exact lower rank from original two norm points, independently replayed.
P=[(Q(61,9),Q(-334,27)),(Q(12),Q(-35))]
for u,v in P:check(v*v==u**3-66*u+289)
def add(P,Q,p):
    if P is None:return Q
    if Q is None:return P
    x,y=P; u,v=Q
    if x==u and (y+v)%p==0:return None
    num,den=(3*x*x-66,2*y) if x==u else (v-y,u-x)
    m=num*pow(den%p,-1,p)%p; w=(m*m-x-u)%p
    return (w,(m*(x-w)-y)%p)
def mul(n,P,p):
    R=None
    for _ in range(n):R=add(R,P,p)
    return R
remain=set(product(range(3),repeat=2))
for p,order in [(5,8),(11,12),(41,51)]:
    check((-16*(4*(-66)**3+27*289**2))%p!=0)
    E=[None]+[(x,y) for x in range(p) for y in range(p) if (y*y-x*x*x+66*x-289)%p==0]
    check(len(E)==order); im={mul(3,T,p) for T in E}
    pts=[tuple(t.numerator*pow(t.denominator,-1,p)%p for t in T) for T in P]
    remain={(a,b) for a,b in remain if add(mul(a,pts[0],p),mul(b,pts[1],p),p) in im}
check(remain=={(0,0)})
print(f'{checks}/{checks} exact checks PASS; 75 ideal generators, 74 independent principal parity relations; mod-3 independence PASS')
