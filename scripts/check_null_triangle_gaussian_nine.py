from itertools import product, permutations, combinations
from fractions import Fraction as F
import sympy as s

def req(ok):
    if not ok: raise AssertionError('geometry contract failed')
T=(-1,0,1)
def bal(x): return (x+1)%3-1
def d(a,b): return next((len(a)-k for k,(x,y) in enumerate(zip(a,b)) if x!=y),0)
def shift(p,k,sg): return p[:k]+(bal(p[k]+sg),)+p[k+1:]
def rot(p,i,j):
    q=list(p); q[i],q[j]=-p[j],p[i]; return tuple(q)
def chart(p,i,j): return tuple(p[k] for k in range(9) if k not in (i,j))+(p[i],p[j])
def unchart(c,i,j):
    r=iter(c[:-2]); return tuple(c[-2] if k==i else c[-1] if k==j else next(r) for k in range(9))
N=faces=paths=0
for p in product(T,repeat=9):
    c=chart(p,7,8); req(unchart(c,7,8)==p)
    q=rot(p,7,8); req(rot(rot(rot(q,7,8),7,8),7,8)==p and q[:7]==p[:7])
    X=lambda a:shift(a,len(a)-2,1)
    Y=lambda a:shift(a,len(a)-1,1)
    R=lambda a:(0,)+a
    e=Y(X(c)); req(e==X(Y(c)) and shift(shift(e,8,-1),7,-1)==c)
    req(d(c,e)==max(d(c,X(c)),d(X(c),e))==max(d(c,Y(c)),d(Y(c),e))==2)
    ops=(X,Y,R)
    for a,b in combinations(range(3),2):
        k=3-a-b
        for z in (c,ops[k](c)):
            req(ops[a](ops[b](z))==ops[b](ops[a](z))); faces+=1
    for order in permutations(range(3)):
        z=c
        for a in order:z=ops[a](z)
        req(z==R(e) and z[1:]==e); paths+=1
    N+=1
S=0
for i,j in permutations(range(9),2):
    for h in ((-1,)*7,(0,)*7,(1,-1,0,1,-1,0,1)):
        for a,b in product(product(T,repeat=2),repeat=2):
            p=unchart(h+a,i,j); q=unchart(h+b,i,j)
            req(chart(p,i,j)==h+a and chart(q,i,j)==h+b)
            rp,rq=rot(p,i,j),rot(q,i,j)
            req(d(chart(rp,j,i),chart(rq,j,i))==d(h+a,h+b)); S+=1

def val(x):
    x=F(x)
    if not x:return float('inf')
    a,b=abs(x.numerator),x.denominator; k=0
    while a%3==0:a//=3;k+=1
    while b%3==0:b//=3;k-=1
    return k
def add(x,y):return (x[0]+y[0],x[1]+y[1])
def mul(x,y):return (x[0]*y[0]-x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def norm(x):return x[0]**2+x[1]**2
def v(x):return min(map(val,x))
def inv(x):return (x[0]/norm(x),-x[1]/norm(x))
G=list(product(map(F,(-3,-1,0,1,3)),repeat=2))+list(product((F(1,3),F(-1,9),F(2,3)),repeat=2))
for x in G:
    req(val(norm(x))==2*v(x))
    if norm(x):req(mul(x,inv(x))==(1,0))
    for y in G:
        req(v(mul(x,y))==v(x)+v(y) and v(add(x,y))>=min(v(x),v(y)))
        if v(x)!=v(y):req(v(add(x,y))==min(v(x),v(y)))

def decode(a):return tuple(sum(a[k+j]*3**(k//2) for k in range(0,len(a),2)) for j in (0,1))
D=0
for n in range(1,4):
    A=list(product(T,repeat=2*n)); values=[decode(a) for a in A]
    for k,a in enumerate(A):
        for l,b in enumerate(A):
            delta=tuple(x-y for x,y in zip(values[k],values[l])); dist=d(a,b)
            req(v(delta)==(n-(dist+1)//2 if dist else float('inf'))); D+=1
    if n>1:
        req(all(tuple(x%3**(n-1) for x in decode(a))==tuple(x%3**(n-1) for x in decode(a[:-2])) for a in A))
u=s.symbols('u'); rho=(-1+s.sqrt(3)*s.I)/2
for alpha,c,e,order in ((s.I,1,0,2),(rho,1,1,3)):
    bar=s.conjugate(alpha); tau=(alpha-u*bar)/(1-u)
    gamma=-1/(c*tau+e); lam=s.simplify((c*alpha+e)**-2)
    req(s.simplify(s.expand_complex(lam**order-1))==0 and lam!=1)
    req(s.simplify(s.together((gamma-alpha)/(gamma-bar)-lam*u))==0)
    for k in range(1,order): req(s.simplify(s.expand_complex(lam**k-1))!=0)
E2,E4,E6=s.symbols('E2 E4 E6'); D4=(E2*E4-E6)/3; D6=(E2*E6-E4**2)/2
req(D6.subs(E6,0)==-E4**2/2 and D4.subs(E4,0)==-E6/3)
print(f'PASS {N} nine-trit squares; {faces} faces; {paths} paths; {S} ordered slice pairs; {len(G)**2} rational Gaussian pairs; {D} residue pairs; two local modular uniformizers and Ramanujan identities')
