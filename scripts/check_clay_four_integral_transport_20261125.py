"""Exact finite controls for RH one-sided criterion, BSD integral isogeny,
NS sextic transport and Hodge middle exterior star. Not universal proofs."""
from fractions import Fraction as Q
from itertools import permutations, combinations, product
import sympy as S
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ

def need(x):
    if not x: raise ArithmeticError('regression failed')

# RH: exact toy reflected quartet, no positive real pole, both signs.
s=S.symbols('s'); z=[a*3+b*S.I/4 for a,b in product((-1,1),repeat=2)]
R=S.cancel(sum(1/(s-S.I*w) for w in z))
for w in z: need(S.simplify(S.limit((s-S.I*w)*R,s,S.I*w))==1)
need(S.Poly(S.denom(R),s).count_roots(0,S.oo)==0)
for n in range(1,9):
    need(S.cos(3*(2*n*S.pi/3))==1 and S.cos(3*((2*n+1)*S.pi/3))==-1)
print('RH 4 poles, no positive real poles, 16 signed phase controls')

# BSD: actual S3 permutation lattices and integral inverse up to [6].
G=list(permutations(range(3))); e=G[0]; a=(1,2,0); b=(1,0,2); r=(0,2,1)
def mul(g,h): return tuple(g[h[i]] for i in range(3))
def cos(H): return sorted(set(tuple(sorted(mul(g,h) for h in H)) for g in G))
C3=cos([e,a,mul(a,a)]); C2=cos([e,b])
A=S.zeros(8,8)
for j,g in enumerate(G):
    A[next(i for i,c in enumerate(C3) if g in c),j]=1
    A[2+next(i for i,c in enumerate(C2) if g in c),j]=1
    A[5+next(i for i,c in enumerate(C2) if mul(g,r) in c),j]=1
for i in range(2): A[i,6]=1
for i in range(2,5): A[i,7]=1
B=6*A.inv(); need(all(x.q==1 for x in B))
need(A*B==B*A==6*S.eye(8)); need(abs(A.det())==18)
need([abs(t) for t in smith_normal_form(A,domain=ZZ).diagonal()]==[1]*6+[3,6])
def perm(g,items,action):
    return S.Matrix(len(items),len(items),lambda i,j:int(items[i]==action(g,items[j])))
for g in G:
    L=S.diag(perm(g,G,mul),S.eye(2))
    f=lambda g,c:tuple(sorted(mul(g,h) for h in c))
    T=S.diag(perm(g,C3,f),perm(g,C2,f),perm(g,C2,f))
    need(A*L==T*A and B*T==L*B)
print('BSD integral det',A.det(),'SNF',[abs(t) for t in smith_normal_form(A,domain=ZZ).diagonal()],'12 equivariance checks, two [6] compositions')

# NS: actual infinite-horizon five-leg normal form symbol (nu=1).
def dot(x,y): return sum(a*b for a,b in zip(x,y))
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def proj(p,v):
    c=Q(dot(p,v),dot(p,p)); return tuple(x-c*y for x,y in zip(v,p))
def mult(s,v): return tuple(s*x for x in v)
def symbol(P,V):
    # include all incoming Leray projections, one first merger, fixed slot 0.
    V=[proj(p,v) for p,v in zip(P,V)]
    k=add(P[0],P[1]); w=mult(dot(P[1],V[0]),proj(k,V[1]))
    p=[k]+P[2:]; v=[w]+V[2:]; x=add(p[0],p[1]); y=add(p[2],p[3])
    a=dot(x,x); lam=sum(dot(k,k) for k in p); b=sum(dot(k,k) for k in P)
    return -2*Q(lam-a,a*lam*lam*b)*dot(x,v[0])*dot(y,v[2])*dot(proj(x,v[1]),proj(y,v[3]))
P0=[(3,-1,3),(-1,2,-2),(1,-3,-3),(0,-2,1),(-3,4,1)]
V=[(-5,27,14),(22,1,-10),(0,1,-1),(0,-6,-12),(41,32,-5)]
nonzero=0
for d in (16,32,64,128):
    for j in range(3):
        ell=tuple(Q(int(k==j),d) for k in range(3)); w=tuple(int(k==(j+1)%3) for k in range(3))
        P=P0[:4]+[add(P0[4],mult(-1,ell))]; base=symbol(P,V)
        need(dot(ell,w)==0 and sum(dot(p,w) for p in P)==0)
        vals=[]
        for i in range(5):
            R=P[:]; R[i]=add(R[i],ell)
            v=symbol(R,V); vals.append((dot(P[i],w),v))
            for scale in (2,3): need(symbol([mult(scale,p) for p in R],V)*scale**3==v)
        full=sum(a*v for a,v in vals); diff=sum(a*(v-base) for a,v in vals)
        need(full==diff); nonzero+=int(full!=0)
need(nonzero>0)
# Elementary exponent breakpoints for low and far sectors.
need(Q(3,2)+Q(5,2)*Q(1,5)==2 and Q(4)-2*Q(2)==0)
print('NS 12 signed cancellations, 120 homogeneous symbol checks, nonzero',nonzero)

# Hodge: middle exterior operator for a diagonal F-valued form.
# Use Q[x]/(x^3+x^2-2*x-1); coefficient operations are exact.
x=S.symbols('x'); f=x**3+x**2-2*x-1
q=[1+x*x,2+x*x,3+x*x,4+x*x,5+x*x,6+x*x]
red=lambda p:S.rem(S.expand(p),f,x)
det=red(S.prod(q)); basis=list(combinations(range(6),3)); J=S.zeros(20); H=S.zeros(20)
for i,I in enumerate(basis):
    K=tuple(k for k in range(6) if k not in I); j=basis.index(K)
    sign=(-1)**sum(a>b for a in I for b in K)
    H[i,i]=red(S.prod(q[k] for k in I))
    J[j,i]=sign*H[i,i]
need((J*J+det*S.eye(20)).applyfunc(red)==S.zeros(20))
need((J.T*H+H*J).applyfunc(red)==S.zeros(20))
need(S.trace(J)==0)
R=S.diag(*[(-1)**int(0 in I) for I in basis]); need(R*J*R==-J)
for i,I in enumerate(basis):
    K=tuple(k for k in range(6) if k not in I); j=basis.index(K)
    sign=(-1)**sum(a>b for a in I for b in K)
    need(red((H*J)[j,i]-sign*det)==0)
print('Hodge 20 relative basis columns, star square, skew adjoint, reflection odd and volume recovery')
