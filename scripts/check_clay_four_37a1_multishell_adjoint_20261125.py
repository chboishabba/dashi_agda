"""Finite source controls, not a Selmer solver, PDE evolution or Chow computation."""
from itertools import combinations,product
import sympy as S

def need(ok):
    if not ok: raise ArithmeticError('exact control failed')

x=S.symbols('x');h=-x*x-2*x
need(S.expand(h*h+h-x**3+x)==S.expand(x*((x+1)**3-2)))
a=S.symbols('a');need(S.rem((1-a*a)**2+(1-a*a)-(a-1)**3+(a-1),a**3-2,a)==0)
need(h.subs(x,0)==0)
# Reduction on y^2+y=x^3-x, retaining actual inverse (x,-1-y).
counts=[];witness=None
for p in (2,3,5,7,11,13,17,19,23,29,31,41,43):
    pts=[None]+[(x,y) for x,y in product(range(p),repeat=2) if (y*y+y-x**3+x)%p==0]
    def add(P,Q):
        if P is None:return Q
        if Q is None:return P
        a,b=P;c,d=Q
        if a==c and (b+d+1)%p==0:return None
        m=((d-b)*pow(c-a,-1,p) if a!=c else (3*a*a-1)*pow(2*b+1,-1,p))%p
        r=(m*m-a-c)%p
        return r,(-1-b-m*(r-a))%p
    G=(0,p-1);three={add(add(P,P),P) for P in pts}
    if G not in three and witness is None:witness=p
    counts.append((p,len(pts),len(three),G not in three))
need(witness is not None)
print('BSD 37a1 norm polynomial; non-3-divisibility witness',witness,'counts',counts)

# Cross-defect formula on actual signed vector slots.
def cross(a,b):return (a[1]*b[2]-a[2]*b[1],a[2]*b[0]-a[0]*b[2],a[0]*b[1]-a[1]*b[0])
def add(*xs):return tuple(sum(v) for v in zip(*xs))
def sc(a,s):return tuple(s*v for v in a)
vectors=list(product((-1,0,1),repeat=3));n=0
for a,b in product(vectors,repeat=2):
    for l,m in product((-2,-1,1,2),repeat=2):
        r=(a[1],a[2],a[0]);s=(b[2],b[0],b[1])
        lhs=add(cross(a,add(sc(b,m),s)),cross(b,add(sc(a,l),r)))
        rhs=add(sc(cross(a,b),m-l),cross(a,s),cross(b,r))
        need(lhs==rhs);n+=1
print('NS',n,'cross-defect controls, no evolution')

# Six split Clifford generators on 3-pair Fock module; half-spin rank4.
def gamma(i,m):
    j=i//2; s=(-1)**((m&((1<<j)-1)).bit_count())
    if i%2 and m&(1<<j):s=-s
    return s,m^(1<<j)
for parity in (0,1):
    states=[m for m in range(8) if m.bit_count()%2==parity]
    pairs=list(combinations(range(6),2)); Bs=[]
    for i,j in pairs:
        M=S.zeros(4)
        for c,m in enumerate(states):
            s,n=gamma(j,m);t,n=gamma(i,n);M[states.index(n),c]=s*t
        need(S.trace(M)==0); Bs.append(M)
    G=S.Matrix(15,15,lambda i,j:S.trace(Bs[i]*Bs[j]))
    expected=S.diag(*[-4*(-1)**(i+j) for i,j in pairs])
    need(G==expected and G.rank()==15)
    need(S.Matrix.hstack(*[S.Matrix(16,1,list(M)) for M in Bs]).rank()==15)
    # Exact trace-dual recovery on all matrix units, plus scalar spectator trace.
    for i,j in product(range(4),repeat=2):
        M=S.zeros(4);M[i,j]=1
        R=sum((S.trace(M*B)/G[k,k]*B for k,B in enumerate(Bs)),S.zeros(4))
        need(R==M-S.trace(M)*S.eye(4)/4)
print('Hodge 2 chirality sectors; 450 trace-Gram entries, 32 trace-dual recoveries; adjoint rank15')
