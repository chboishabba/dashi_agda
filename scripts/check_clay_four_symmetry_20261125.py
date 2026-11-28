"""Exact controls for four source-symmetry reductions; not universal Clay proofs."""
from fractions import Fraction as Q
from itertools import permutations, product
import sympy as S
import random

def need(b):
    if not b: raise ArithmeticError('regression failed')

# RH: quartet toy with nonreal spectral pair, resolvent and two-shift form.
s=S.symbols('s'); I=S.I
Z=[a*3+b*I/4 for a,b in product((-1,1),repeat=2)]
F=sum(1/(s-I*z) for z in Z)
for z in Z:
    need(S.simplify(S.limit((s-I*z)*F,s,I*z))==1)
# For t=2pi/3, 4cos(3t)cosh(t/4)>4, hence minus-shift negative.
need(S.cos(3*(2*S.pi/3))==1)
need(S.cosh(S.pi/6).is_positive)
# exact inequality follows cosh(x)-1=2sinh(x/2)^2 >0 for x>0.
need(S.simplify(S.cosh(S.pi/6)-1-2*S.sinh(S.pi/12)**2)==0)
print('RH quartet resolvent poles 4; exact negative difference form')

# BSD: S3 permutation-character identity [regular]+2[trivial]=[C3 cosets]+2[C2 cosets].
G=list(permutations(range(3))); e=tuple(range(3)); a=(1,2,0); b=(1,0,2)
def mul(p,q): return tuple(p[q[i]] for i in range(3))
H3={e,a,mul(a,a)}; H2={e,b}
def cosets(H):
    return list({frozenset(mul(g,h) for h in H) for g in G})
def fix(g,C): return sum(frozenset(mul(g,h) for h in c)==c for c in C)
for g in G: need(6*(g==e)+2==fix(g,cosets(H3))+2*fix(g,cosets(H2)))
# Actual standard module zero-sum plane in permutation rep, basis e0-e2,e1-e2.
U=S.Matrix([[1,0],[0,1],[-1,-1]])
def pm(g): return S.Matrix(3,3,lambda i,j:int(i==g[j]))
A={g:(pm(g)*U)[:2,:] for g in G}
for p,q in product(G,repeat=2): need(A[p]*A[q]==A[mul(p,q)])
for g in G: need(U*A[g]==pm(g)*U)
need((S.eye(2)+A[b]).rank()==1)
need(sum((A[g] for g in H3),S.zeros(2))==S.zeros(2))
# Exact integral projector controls away from 2,3.
for ell in (5,7,11,13):
    for n in (1,2,3):
        m=ell**n
        for x,y in product(range(3),repeat=2):
            v=S.Matrix([x,y]); P=(S.eye(2)+A[b])*pow(2,-1,m)
            need(all(int(t)%m==0 for t in P*P*v-P*v))
print('BSD S3 6 character values, 36 composition laws, 108 modular projector controls')

# NS: full signed coordinate permutation action, actual old 5-wave symbol.
P0=[(3,-1,3),(-1,2,-2),(1,-3,-3),(0,-2,1),(-3,4,1)]
V0=[tuple(Q(x,d) for x in v) for v,d in [((-5,27,14),19),((22,1,-10),9),((0,1,-1),1),((0,-6,-12),5),((41,32,-5),26)]]
O=[(p,sig) for p in G for sig in product((-1,1),repeat=3)]; Id=(e,(1,1,1))
def act(g,x): p,sg=g; return tuple(sg[i]*x[p[i]] for i in range(3))
def add(x,y): return tuple(a+b for a,b in zip(x,y))
def neg(x): return tuple(-a for a in x)
def dot(x,y): return sum(a*b for a,b in zip(x,y))
def proj(p,v):
    c=Q(dot(p,v),dot(p,p));return tuple(x-c*y for x,y in zip(v,p))
def symbol(ps,vs):
    x=add(ps[0],ps[1]); y=add(ps[2],ps[3]); a=dot(x,x); lam=sum(dot(p,p) for p in ps)
    need(a>0 and dot(y,y)>0)
    c=-2*Q(lam-a,a*lam*lam)*dot(x,vs[0])*dot(y,vs[2])*dot(proj(x,vs[1]),proj(y,vs[3]))
    return c,lam
# Integer centres scaled by 10000. Anchor final group element to identity.
# Meet-in-middle: 48^4 combinations reduced to two 48^2 pair tables.
rng=random.Random(369); den=10000
for trial in range(100):
    P=[tuple(den*x+rng.randrange(-50,51) for x in p) for p in P0[:4]]
    P.append(tuple(-sum(p[i] for p in P) for i in range(3)))
    orb=[[act(g,p) for g in O] for p in P]
    if len(set(sum(orb,[])))!=240: continue
    table={}
    for i,j in product(range(48),repeat=2): table.setdefault(add(orb[0][i],orb[1][j]),[]).append((i,j))
    hits=[]
    for k,l in product(range(48),repeat=2):
        target=neg(add(add(orb[2][k],orb[3][l]),P[4]))
        hits.extend((i,j,k,l) for i,j in table.get(target,[]))
    idx=O.index(Id)
    if hits==[(idx,)*4]:break
else: raise ArithmeticError('no generic point')
Pint=P; P=[tuple(Q(x,den) for x in p) for p in Pint]; V=[proj(p,v) for p,v in zip(P,V0)]
need(all(dot(p,v)==0 for p,v in zip(P,V)))
terms=[]; mags=[]
for a,b,*rest in permutations(range(5)):
    k=add(P[a],P[b]); w=tuple(dot(P[b],V[a])*v for v in proj(k,V[b]))
    for slot in range(4):
        ps=[P[j] for j in rest];vs=[V[j] for j in rest];ps.insert(slot,k);vs.insert(slot,w)
        c,lam=symbol(ps,vs);terms.append((c,lam))
        mags.extend(dot(p,p) for p in ps+[add(ps[0],ps[1]),add(ps[2],ps[3])])
C=sum(c for c,l in terms); err=sum(abs(c)/2**int(l) for c,l in terms)
need(min(mags)>=1 and max(mags)<=64 and err<abs(C)/2)
# Check actual projector/cross/symbol covariance on one complete ordered 4-slot block.
for g in O:
    for a,b,*rest in [tuple(range(5))]:
        k=add(P[a],P[b]); w=tuple(dot(P[b],V[a])*v for v in proj(k,V[b]))
        need(proj(act(g,k),act(g,V[b]))==act(g,proj(k,V[b])))
        for slot in range(4):
            ps=[P[j] for j in rest];vs=[V[j] for j in rest];ps.insert(slot,k);vs.insert(slot,w)
            need(symbol([act(g,p) for p in ps],[act(g,v) for v in vs])==symbol(ps,vs))
print('NS centres numerator/10000',Pint,'trial',trial)
print('NS 240 distinct centres; 4608 meet-in-middle pair states, 1 anchored resonance, 48 full resonances')
print('NS 480 ordered terms, 192 transformed symbols, C_inf',float(C),'error',float(err),'range',float(min(mags)),float(max(mags)))

# Hodge: actual abstract relative determinant obstruction on F^6, trace form over Q.
x=S.symbols('x'); f=x**3+x**2-2*x-1
M=S.Matrix([[0,0,1],[1,0,2],[0,1,-1]])
need(M.charpoly(x).as_expr()==f)
H=S.Matrix(3,3,lambda i,j:S.trace(M**(i+j)))
need(H.det()==49 and M.T*H==H*M)
# F-linear reflection diag(-1,1,..,1) preserves all trace pairings and field actions.
R=S.diag(-S.eye(3),*([S.eye(3)]*5)); Afield=S.diag(*([M]*6)); Qtrace=S.diag(*([H]*6))
need(R.T*Qtrace*R==Qtrace and R*Afield==Afield*R)
# Relative determinant sign -1 at all three embeddings; absolute determinant -1 also.
need(R.det()==-1)
# Any tensor generated by pairings & field maps invariant; finite checks of generator pairs.
for j in range(3): need(R.T*(Qtrace*Afield**j)*R==Qtrace*Afield**j)
print('Hodge 18D field/trace/reflection identities, determinant sign -1; 3 paired generators')
