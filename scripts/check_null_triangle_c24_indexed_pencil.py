from itertools import product, permutations
from collections import Counter
import sympy as s

def req(x):
    if not x: raise AssertionError('C24 indexed pencil')
# O_K/(pi^2) = F9[eps]/eps^2, i^2=-1, eps=pi.
Z=(0,0); U=(1,0); G=(1,1)
def add(a,b): return tuple((x+y)%3 for x,y in zip(a,b))
def neg(a): return tuple(-x%3 for x in a)
def mul(a,b): return ((a[0]*b[0]-a[1]*b[1])%3,(a[0]*b[1]+a[1]*b[0])%3)
def sc(k,a): return tuple(k*x%3 for x in a)
P=[U]
for j in range(7): P.append(mul(P[-1],G))
req(len(set(P))==8 and P[4]==neg(U) and mul(P[-1],G)==U)
# Chart d indexes the pole line; units retain all 8x3 possibilities.
units=[(a,sc(k,a)) for a in P for k in range(3)]
charts=[[(d,a,b) for a,b in units+[(Z,Z),(Z,P[d]),(Z,neg(P[d]))]] for d in range(4)]
states=sum(charts,[])
def enc(q):
    d,a,b=q
    if a!=Z: return (d,'u',P.index(a),next(k for k in range(3) if sc(k,a)==b))
    return (d,'p',0, next(k for k in range(3) if sc(k,P[d])==b))
def dec(q):
    d,t,j,k=q
    return (d,P[j],sc(k,P[j])) if t=='u' else (d,Z,sc(k,P[d]))
def x(q):
    d,a,b=q; return ((d+1)%4,mul(G,a),mul(G,b))
def y(q):
    d,a,b=q; return (d,a,add(a,b))
def X(q):
    d,t,j,k=q
    return ((d+1)%4,t,(j+1)%8,k) if t=='u' else ((d+1)%4,t,0,(-k if d==3 else k)%3)
def Y(q):
    d,t,j,k=q; return (d,t,j,(k+1)%3 if t=='u' else k)
def step(q,axis,encoded):
    if axis=='z': return enc(q), True
    return ({'x':X,'y':Y} if encoded else {'x':x,'y':y})[axis](q),encoded
def run(q,word,encoded=False):
    for a in word: q,encoded=step(q,a,encoded)
    return q,encoded
faces=paths=0
for q in states:
    req(dec(enc(q))==q and x(q) in states and y(q) in states)
    for a,b,c in [('x','y','z'),('x','z','y'),('y','z','x')]:
        req(run(q,a+b)==run(q,b+a)); faces+=1
        v,e=run(q,c); req(run(v,a+b,e)==run(v,b+a,e)); faces+=1
    endpoints=[run(q,''.join(w)) for w in permutations('xyz')]
    for e in endpoints: req(e==endpoints[0]); paths+=1
    r=q
    for j in range(24):
        r=x(y(r))
        if j==11: req(r==(q[0],neg(q[1]),neg(q[2])))
    req(r==q)
# The 27 chart is not scalar-invariant; four pole lines are forced.
union={q[1:] for q in states}; req(len(union)==33)
req(len({q[1:] for q in charts[0]})==27)
req(x((0,Z,U))[2]==G and G not in (Z,U,neg(U)))
# Each chart: 9 residue fibres of size 3, strong triangle by agreement.
def dist(a,b): return 0 if a==b else 1 if a[0]==b[0] else 2
triples=0
for chart in charts:
    pts=[q[1:] for q in chart]
    req(Counter(Counter(a for a,b in pts).values())=={3:9})
    for a,b,c in product(pts,repeat=3):
        u,v,w=dist(a,b),dist(b,c),dist(a,c)
        req(w<=max(u,v) and (u==v or w==max(u,v))); triples+=1
# 24 unit states, 12 antipodal pairs, R on oriented basis is negacyclic.
r=(0,U,Z); orbit=[]
for k in range(24): orbit.append(r[1:]); r=x(y(r))
req(len(set(orbit))==24 and all(orbit[k+12]==tuple(map(neg,orbit[k])) for k in range(12)))
R=s.zeros(12)
for k in range(11): R[k+1,k]=1
R[0,11]=-1
v=s.Symbol('v'); req(R**12==-s.eye(12) and R.charpoly(v).as_expr()==v**12+1)
# Field lift eta=(1+i)/sqrt(-2), eta^2=-i, eta^4=-1.
i=s.I; req(s.simplify((1+i)**2/(-2))==-i)
# Same unit phase action is not an incidence collineation of PG(2,3).
# F9 coordinates a, t = sign(a)*k, plus fixed projective pole.
def orient(a): return 1 if P.index(a)<4 else -1
def proj(q):
    d,t,j,k=enc(q)
    if t=='p': return None if k==0 else (0,0,1)
    a=P[j]; sign=orient(a); return tuple(sc(sign,a))+(k,)
def collinear(p,q,r): return int(s.Matrix([p,q,r]).det())%3==0
pp=[q for q in charts[0] if q[1]!=Z and orient(q[1])==1]+[(0,Z,U)]
fail=0
for a,b,c in __import__('itertools').combinations(pp,3):
    if collinear(proj(a),proj(b),proj(c))!=collinear(proj(y(a)),proj(y(b)),proj(y(c))): fail+=1
req(fail>0)
print(f'PASS {len(states)} indexed states; {faces} faces; {paths} endpoint routes; {triples} strong triangles; 33 scalar-closure points; 24 unit orbit; {fail} ternary incidence mismatches')
