"""Exact tower, helical polarization and local spin-involution controls.
No native kernel, actual Selmer descent, PDE evolution or Chow computation.
"""
from itertools import permutations, product
import sympy as S
from sympy.matrices.normalforms import smith_normal_form
from sympy.polys.domains import ZZ


def need(b):
    if not b:
        raise ArithmeticError('exact control failed')

G=list(permutations(range(3))); e,a,b,r=G[0],(1,2,0),(1,0,2),(0,2,1)
def mul(g,h):return tuple(g[h[i]] for i in range(3))
def cosets(H):return sorted(set(tuple(sorted(mul(g,h) for h in H)) for g in G))
C3,C2=cosets([e,a,mul(a,a)]),cosets([e,b]); A=S.zeros(8)
for j,g in enumerate(G):
    A[next(i for i,c in enumerate(C3) if g in c),j]=1
    A[2+next(i for i,c in enumerate(C2) if g in c),j]=1
    A[5+next(i for i,c in enumerate(C2) if mul(g,r) in c),j]=1
for i in range(2):A[i,6]=1
for i in range(2,5):A[i,7]=1
pi=S.eye(8)[7,:]; D=6*A.inv(); C=3*pi*A.inv()
need(all(x.is_Integer for x in D) and C==S.Matrix([[0,0,1,1,1,-1,-1,-1]]))
for n in range(1,9):
    m=3**n; An=3**(n-1)*A; z=pow(2,-1,m)
    need(C*An==m*pi and An*D==2*m*S.eye(8) and D*An==2*m*S.eye(8))
    need(pi*D==2*C and (2*z-1)%m==0)
    sn=smith_normal_form(An,domain=ZZ)
    need(sorted(abs(sn[i,i]) for i in range(8))==[3**(n-1)]*6+[m,2*m])
    if n>1:need(An==3*(3**(n-2)*A))
    need((1+m)%2==0 and (1+m)%m==1)
print('BSD 8 integral tower levels; exact norm, dual and Smith identities')

# Unit helical polarizations in a common oriented triad plane.
I=S.I; n=S.Matrix([0,0,1]); count=0
for h in [S.Rational(1,5),S.Rational(1,2),S.Rational(1),S.Rational(2),S.Rational(5)]:
    c=(1-h*h)/(1+h*h); s=2*h/(1+h*h)
    for r,t in product([1,2,5],repeat=2):
        p=S.Matrix([r,0,0]); q=t*S.Matrix([c,s,0]); k=p+q; k2=k.dot(k)
        L=S.eye(3)-k*k.T/k2
        for u,v in product([-1,1],repeat=2):
            hp=(n.cross(p/r)+I*u*n)/S.sqrt(2); hq=(n.cross(q/t)+I*v*n)/S.sqrt(2)
            z=L*hp.cross(hq); norm=S.simplify((z.conjugate().T*z)[0]); diff=v*t-u*r; total=u*r+v*t
            need(S.simplify(norm-s*s*(1+total**2/k2)/4)==0)
            m2=S.simplify(diff**2*norm/k2); need(0<=m2<=1)
            need(S.simplify(I*p.cross(hp)-u*r*hp)==S.zeros(3,1))
            count+=1
X,Y=S.symbols('X Y'); need(S.expand((X-Y)**2-X*(X-1)*(1-Y*Y)-X*(1-Y)**2-(X-1)**2*Y*Y)==0)
print('NS',count,'exact helical polarization/cap controls; polynomial gap identity')

# Complex Dirac matrices via Pauli tensor products; restrict to even/odd Fock parity.
X=S.Matrix([[0,1],[1,0]]); Y=S.Matrix([[0,-I],[I,0]]); Z=S.diag(1,-1); E=S.eye(2)
g=[]
for j in range(3):
    for P in (X,Y):g.append(S.kronecker_product(*([Z]*j+[P]+[E]*(2-j))))
for signature in ((1,1,-1,-1,-1,-1),(-1,)*6):
    gamma=[a if s==1 else I*a for a,s in zip(g,signature)]
    H=gamma[2]*gamma[3]*gamma[4]*gamma[5] if signature[0]==1 else S.eye(8)
    J=gamma[0]*gamma[1] if signature[0]==1 else I*S.eye(8)
    need(H.H==H and J*J==-S.eye(8) and J.H*H*J==H)
    for i,j in product(range(6),repeat=2):
        need(gamma[i]*gamma[j]+gamma[j]*gamma[i]==(2*signature[i]*S.eye(8) if i==j else S.zeros(8)))
        need((gamma[i]*gamma[j]).H*H==H*gamma[j]*gamma[i])
    for parity in (0,1):
        inds=[m for m in range(8) if m.bit_count()%2==parity]
        Hp=H.extract(inds,inds); Jp=J.extract(inds,inds)
        need(Hp.det()!=0 and Jp*Jp==-S.eye(4))
        need(I*Hp*Jp in (S.eye(4),-S.eye(4)))
        need(Hp.eigenvals()==({1:2,-1:2} if signature[0]==1 else {1:4}))
print('Hodge 2 real signatures x 2 half-spin sectors, reversion and definite Riemann form controls')
