"""Exact original-to-adapted Schr chart change for selected ATLAS source.
Reuse check_toe_atlas_mirror; no actual Monster multiplicity identification.
"""
from check_toe_atlas_mirror import np, P, Pa, inv, Js, Coc, rank, m, r
from itertools import product
from collections import deque

def eq(a,b): return bool(np.all((a-b)%3==0))
X=np.array(list(product(range(3),repeat=6)),dtype=np.int64)
N=len(X); digits=3**np.arange(5,-1,-1)
def idx(x): return (x%3)@digits
A=inv(Pa)@P%3
assert eq(A.T@Js@A,Js)
E=(A.T@Coc@A-Coc)%3
assert eq(E,E.T) and eq(2*(E+E.T),E)
def lift(G,v):
    d=(G.T@Coc@G-Coc)%3
    return (G@v%3,int(2*v@d@v%3))
def q(v):return int(2*v@E@v%3)
I=np.eye(12,dtype=np.int64)
# Vacuum fixed by transported modulation generators. -1 means zero.
gens=[lift(A,e) for e in I[6:]]
visited=set(); accepted=[]
for start in range(N):
    if start in visited: continue
    vals={start:0}; queue=deque([start]); valid=True
    while queue:
        i=queue.popleft(); x=X[i]
        for v,z in gens:
            a,b=v[:6],v[6:]; j=int(idx(x+a)); k=int((vals[i]+z+b@x)%3)
            if j in vals:
                valid &= vals[j]==k
            else: vals[j]=k;queue.append(j)
    visited.update(vals)
    if valid:accepted.append(vals)
assert len(accepted)==1
vac=np.full(N,-1,dtype=np.int64)
for i,k in accepted[0].items():vac[i]=k
K=np.full((N,N),-1,dtype=np.int64)
for j,x in enumerate(X):
    v,z=lift(A,np.r_[x,np.zeros(6,dtype=int)])
    a,b=v[:6],v[6:]; rows=idx(X+a); ok=vac>=0
    K[rows[ok],j]=(vac[ok]+z+X[ok]@b)%3
support=3**rank(A[:6,6:]); assert support==243
assert np.all((K>=0).sum(axis=0)==support)
assert np.all((K>=0).sum(axis=1)==support)
# coefficient exponents: W(a,b,z)e_x = zeta^(s*(z+b.x)) e_(x+a)
# A common normalization 1/[9(1+2*zeta^s)] has squared modulus 1/243.
checks=0
for s in (1,2):
    H=np.where(K>=0,s*K%3,-1)
    for e in I:
        v,z=lift(A,e); a,b=v[:6],v[6:]; c,d=e[:6],e[6:]
        left=H[:,idx(X+c)]
        left=np.where(left>=0,(left+s*(X@d)[None,:])%3,-1)
        right=H[idx(X-a),:]
        right=np.where(right>=0,(right+s*(z+(X-a)@b)[:,None])%3,-1)
        assert np.array_equal(left,right);checks+=N*N
# exact orthogonality: root counts for each pair of columns (vectorized).
for j in range(N):
    valid=(K[:,j,None]>=0)&(K>=0)
    diff=(K-K[:,j,None])%3
    counts=np.array([(valid&(diff==k)).sum(axis=0) for k in range(3)])
    assert np.all(counts[1]==counts[2])
    desired=np.zeros(N,dtype=int);desired[j]=support
    assert np.array_equal(counts[0]-counts[2],desired)
# Composition of canonical quadratic lifts follows by telescoping defects.
# Verify the same source words are conjugated in both charts, including q.
for source,lam in ((m,2),(r,1)):
    Go=inv(P)@source@P%3; Ga=inv(Pa)@source@Pa%3
    assert eq(A@Go,Ga@A)
    Do=(Go.T@Coc@Go-lam*Coc)%3; Da=(Ga.T@Coc@Ga-lam*Coc)%3
    assert eq(Do+Go.T@E@Go,lam*E+A.T@Da@A)
# Exact conjugate phase gauge: K_- = conjugate K_+ (including denominator).
print('chart upper-right rank',rank(A[:6,6:]),'support',support,'vacuum position',min(accepted[0]))
print('PASS',checks,'generator entries;',N*N,'column inner products; source mirror/rotation cocycle squares')
