"""Direct original-chart selected D4 regression over Z[zeta], no source Hom claim."""
import check_toe_atlas_rechart as c
import check_toe_atlas_weil as w
import numpy as np

def roots(k):
    return ((k==0).astype(np.int64)-(k==2), (k==1).astype(np.int64)-(k==2))
def conj(z):
    a,b=z; return a-b,-b
def adj(z): return tuple(t.T for t in conj(z))
def mul(z,t):
    a,b=z; d,e=t
    h=a@d; j=b@e
    return h-j,(a+b)@(d+e)-h-2*j
def scale(z,n): return tuple(n*a for a in z)
def same(z,t): return all(np.array_equal(a,b) for a,b in zip(z,t))
def entrymul(z,t):
    a,b=z; d,e=t
    return a*d-b*e,a*e+b*d-b*e
X=c.X; N=c.N; I=np.eye(N,dtype=np.int64)
identity=(I,np.zeros_like(I))
P=(I[:,c.idx(-X)],np.zeros_like(I))
k=roots(c.K); f=roots(w.K)
# K+ = k/d+, K- = conjugate(k)/d-, d-=-d+, |d|²=243.
# R+ = k† f k/(243*27), S(+ -> -) = k^T k/(-243).
assert same(mul(adj(k),k),scale(identity,243))
R=mul(mul(adj(k),f),k); rd=243*27
S=scale(mul(tuple(a.T for a in k),k),-1); sd=243
# Direct original-coordinate Heisenberg covariance, including central phase.
checks=0
for source,lam,mat in [(c.r,1,R),(c.m,2,S)]:
    G=c.inv(c.P)@source@c.P%3
    defect=(G.T@c.Coc@G-lam*c.Coc)%3
    for phase in (1,2):
        H=mat if phase==1 else conj(mat)
        outphase=phase*lam%3
        for e in c.I:
            a,b=e[:6],e[6:]; v=G@e%3; u,t=v[:6],v[6:]; z=2*e@defect@e%3
            left=entrymul(tuple(h[:,c.idx(X+a)] for h in H),roots((phase*(X@b)%3)[None,:]))
            right=entrymul(tuple(h[c.idx(X-u),:] for h in H),roots((outphase*(z+(X-u)@t)%3)[:,None]))
            assert same(left,right); checks+=N*N
# Exact group relations, denominators retained; avoid overflow from fourth powers.
assert same(mul(R,R),scale(P,rd*rd))
assert same(mul(adj(R),R),scale(identity,rd*rd))
assert same(mul(conj(S),S),scale(identity,sd*sd))
# S+ R+ = R-^{-1} S+.
assert same(mul(S,R),mul(adj(conj(R)),S))
print('PASS composed original-chart covariance',checks,'entry checks; R² parity, unitarity, S², dihedral')
print('R support range',np.count_nonzero((R[0]!=0)|(R[1]!=0),axis=0).min(),np.count_nonzero((R[0]!=0)|(R[1]!=0),axis=0).max())
print('S support range',np.count_nonzero((S[0]!=0)|(S[1]!=0),axis=0).min(),np.count_nonzero((S[0]!=0)|(S[1]!=0),axis=0).max())
