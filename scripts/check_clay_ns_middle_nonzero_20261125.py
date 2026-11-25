"""Exact coefficient of original signed quartic nonlinear derivative, not an NS trajectory."""
from fractions import Fraction as Q
from itertools import permutations, product

P=[(3,-1,3),(-1,2,-2),(1,-3,-3),(0,-2,1),(-3,4,1)]
V=[tuple(Q(x,d) for x in v) for v,d in [((-5,27,14),19),((22,1,-10),9),((0,1,-1),1),((0,-6,-12),5),((41,32,-5),26)]]
def need(b):
    if not b: raise ArithmeticError('regression failed')
def dot(a,b): return sum(x*y for x,y in zip(a,b))
def add(a,b): return tuple(x+y for x,y in zip(a,b))
def proj(p,v):
    c=Q(dot(p,v),dot(p,p)); return tuple(x-c*y for x,y in zip(v,p))
def symbol(ps,vs):
    x=add(ps[0],ps[1]); y=add(ps[2],ps[3]); a=dot(x,x); lam=sum(dot(p,p) for p in ps)
    need(a>0 and dot(y,y)>0)
    c=-2*Q(lam-a,a*lam*lam)*dot(x,vs[0])*dot(y,vs[2])*dot(proj(x,vs[1]),proj(y,vs[3]))
    return c,lam
need(all(dot(p,v)==0 for p,v in zip(P,V)))
need(tuple(map(sum,zip(*P)))==(0,0,0))
# For the multilinear amplitude monomial, only all-positive and all-negative labels resonate.
res=[s for s in product((-1,1),repeat=5) if all(sum(s[j]*P[j][i] for j in range(5))==0 for i in range(3))]
need(res==[(-1,)*5,(1,)*5])
slots=[Q(0)]*4; err=Q(0); count=0; mags=[]
for a,b,*rest in permutations(range(5)):
    k=add(P[a],P[b]); w=tuple(dot(P[b],V[a])*v for v in proj(k,V[b]))
    for slot in range(4):
        ps=[P[j] for j in rest]; vs=[V[j] for j in rest]; ps.insert(slot,k); vs.insert(slot,w)
        c,lam=symbol(ps,vs); slots[slot]+=c; err+=abs(c)/2**lam; count+=1
        mags.extend(dot(p,p) for p in ps+[add(ps[0],ps[1]),add(ps[2],ps[3])])
C=sum(slots)
need(C==Q(-60580737938834193827490115793,39526912627930686414456000000))
need(err<abs(C)/2)
need(min(mags)>0)
print('ordered terms',count,'squared shell range',min(mags),max(mags))
print('positive-label infinite-horizon coefficient',C)
print('finite h=1 error upper bound',float(err),'strictly below half coefficient',float(abs(C)/2))
print('real-field mixed coefficient at h=1 nonzero (one imaginary amplitude, conjugate negative labels)')
