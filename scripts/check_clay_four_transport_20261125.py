"""Exact finite regression: signed Fourier transport, quadratic rank-one lattice,
Clifford exterior map, and ramification. Not a PDE/cycle/native-kernel proof."""
from itertools import product, permutations
from fractions import Fraction as Q
from math import prod
import random
import sympy as S

def dot(a,b): return sum(x*y for x,y in zip(a,b))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def proj(p,v):
    c=Q(dot(p,v),dot(p,p))
    return tuple(x-c*y for x,y in zip(v,p))
# The smooth comparable-frequency symbol at infinite auxiliary horizon,
# without the shell bump (which would be 1 in its interior).
def M(ps,vs):
    vs=[proj(p,v) for p,v in zip(ps,vs)]
    a,b,c,d=ps; x=add(a,b); y=add(c,d)
    A=dot(x,x); L=sum(dot(p,p) for p in ps)
    return -2*Q(L-A,A*L*L)*dot(x,vs[0])*dot(y,vs[2])*dot(proj(x,vs[1]),proj(y,vs[3]))
rng=random.Random(369); n=0; nonzero=0
for trial in range(700):
    l=(0,1,0); U=(1,0,1)
    ps=[tuple(rng.randint(-7,7) for _ in range(3)) for _ in range(3)]
    ps.append(tuple(-l[i]-sum(p[i] for p in ps) for i in range(3)))
    vs=[tuple(rng.randint(-4,4) for _ in range(3)) for _ in range(4)]
    if any(dot(p,p)==0 for p in ps): continue
    vs=[proj(p,v) for p,v in zip(ps,vs)]
    shifts=[ps[:i]+[add(ps[i],l)]+ps[i+1:] for i in range(4)]
    if any(not all(dot(p,p) for p in z) or not dot(add(z[0],z[1]),add(z[0],z[1])) or not dot(add(z[2],z[3]),add(z[2],z[3])) for z in [ps]+shifts): continue
    base=M(ps,vs); weights=[dot(p,U) for p in ps]
    assert sum(weights)==-dot(l,U)==0
    direct=sum(c*M(z,vs) for c,z in zip(weights,shifts))
    repaired=sum(c*(M(z,vs)-base) for c,z in zip(weights,shifts))
    assert direct==repaired
    nonzero+=direct!=0; n+=1
assert nonzero>0
print('NS projected signed symbol shifts:',n,'nonzero:',nonzero)
# BSD: full two-descent point and torsion square-class witnesses.
def sc(q):
    q=Q(q); assert q
    sign=-1 if q<0 else 1
    return sign*prod(int(p) for p,e in S.factorint(abs(q.numerator)*q.denominator).items() if e%2)
roots=[0,5,-5]; xx=Q(25,4)
P=tuple(sc(xx-e) for e in roots)
T=[(1,1,1)]
for i,e in enumerate(roots):
    T.append(tuple(sc(prod(e-v for v in roots if v!=e)) if j==i else sc(e-v) for j,v in enumerate(roots)))
assert P==(1,5,5) and P not in T
z=S.sqrt(5); x=2-z;y=4-2*z;s=(3*x*x-1)/(2*y)
assert S.simplify(s*s-2*x)==S.Rational(5,4)
assert S.simplify(s*(x-S.Rational(5,4))-y)==-3*z/8
# Count E(F_9) and E(F_49) directly using F_p[t]/(t^2-5).
counts=[]
for p in (3,7):
    F=list(product(range(p),repeat=2))
    def mul(a,b): return ((a[0]*b[0]+5*a[1]*b[1])%p,(a[0]*b[1]+a[1]*b[0])%p)
    squares={}
    for a in F:squares[mul(a,a)]=squares.get(mul(a,a),0)+1
    c=1
    for a in F:
        a3=mul(mul(a,a),a); c+=squares.get(tuple((x-y)%p for x,y in zip(a3,a)),0)
    counts.append(c)
assert counts==[16,64]
# Rational twist torsion: independent good reductions.
ct=[]
for p in (3,7):ct.append(1+sum((y*y-x*x*x+25*x)%p==0 for x,y in product(range(p),repeat=2)))
assert ct==[4,8]
print('BSD point class',P,'torsion classes',T,'good reduction counts',counts,ct)
# Hodge Clifford volume map: diagonal Clifford algebra, w=e0.
# Multiplication acts on bit-mask basis using e_i e_j=-e_j e_i and e_i^2=q_i.
def cm(a,b,q):
    s=1
    for i in range(len(q)):
        if a>>i&1:
            if (b&((1<<i)-1)).bit_count()%2:s=-s
            if b>>i&1:s*=q[i]
    return a^b,s
checks=0
for m in range(3,7):
    q=[1,1]+[-1]*(m-2)+[-1] # extra direction outside relative block
    w=1; wm=0; ws=1
    for _ in range(m):wm,c=cm(wm,w,q);ws*=c
    volume=(1<<m)-1
    for p in permutations(range(m)):
        perm=(-1)**sum(p[i]>p[j] for i in range(m) for j in range(i+1,m))
        a=0; fac=1
        for i in reversed(p):
            a,b=cm(1<<i,a,q);fac*=b
            a,b=cm(a,w,q);fac*=b
        v,c=cm(volume,wm,q)
        assert a==v and fac==perm*ws*c
        # Right multiplication by w^m is invertible; output recovers volume.
        rec,c2=cm(a,wm,q); assert rec==volume and fac*ws*c2==perm
        checks+=1
print('Hodge exterior-Clifford permutation checks:',checks)
