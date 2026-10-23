#!/usr/bin/env python3
"""Exact local-Python 369 cube modular-dynamics max-cut.
Native Cube27 is 3x3x3 grid; M(x,y,z)=(x+y,x-y,z) mod3.
Do NOT equate geometric 27, cyclic Z/27, or Monster order27.
Requires only Python and SymPy. Computes M-equivariant graph support
cuts and a conditional cube-Laplacian experimental discriminator.
"""
from itertools import product
from collections import Counter
import sympy as s

pts=sorted(product((-1,0,1),repeat=3))
idx={p:i for i,p in enumerate(pts)}
res=lambda a:(a+1)%3-1
M=lambda p:(res(p[0]+p[1]),res(p[0]-p[1]),p[2])
def canon(a,b):return tuple(sorted((a,b)))
def distance(a,b):return sum(abs(x-y) for x,y in zip(a,b))
E={canon(a,b) for a in pts for b in pts if distance(a,b)==1}
act=lambda edges:{canon(M(a),M(b)) for a,b in edges}
assert len(pts)==27 and len(E)==54
assert all(M(M(a))==(-a[0],-a[1],a[2]) for a in pts)
ME=act(E)
assert act(ME)==E
E_local=E&ME
E_complete=E|ME
assert len(E_local)==18 and act(E_local)==E_local
assert len(E_complete)==90 and act(E_complete)==E_complete
assert len(E_complete-E)==36
assert Counter(distance(a,b) for a,b in E_complete-E)==Counter({2:12,3:24})
assert E_local=={canon((x,y,z),(x,y,z+1))
                for x in (-1,0,1) for y in (-1,0,1) for z in (-1,0)}
# All 18 remaining strictly local edges are z-direction only.
# M preserves exactly their nine disjoint 3-site line components.
def connected(edges):
    adj={a:set() for a in pts}
    for a,b in edges:adj[a].add(b);adj[b].add(a)
    unseen=set(pts); sizes=[]
    while unseen:
        component=set();stack=[next(iter(unseen))]
        while stack:
            a=stack.pop()
            if a in component:continue
            component.add(a);unseen.discard(a)
            stack.extend(adj[a]-component)
        sizes.append(len(component))
    return sorted(sizes)
assert connected(E_local)==[3]*9
assert connected(E_complete)==[27]
def lap(edges):
    L=s.zeros(27)
    for a,b in edges:
        i,j=idx[a],idx[b]
        L[i,i]+=1;L[j,j]+=1;L[i,j]-=1;L[j,i]-=1
    return L
P=s.zeros(27)
for a,i in idx.items():P[idx[M(a)],i]=1
L=lap(E); Llocal=lap(E_local);Lcomplete=lap(E_complete)
assert P.T*P==s.eye(27)
assert L*P!=P*L
assert Llocal*P==P*Llocal and Lcomplete*P==P*Lcomplete
K=L*P-P*L
assert K.rank()==24 and s.trace(K.T*K)==168
assert Lcomplete-L==lap(E_complete-E)   # positive semidefinite extension
assert (s.trace(L),s.trace(L*L))==(108,558)
assert (s.trace(Llocal),s.trace(Llocal*Llocal))==(36,90)
assert (s.trace(Lcomplete),s.trace(Lcomplete*Lcomplete))==(180,1410)
assert M((1,0,0))==(1,1,0)
assert L[idx[(1,0,0)],idx[(1,0,0)]]==5
assert L[idx[(1,1,0)],idx[(1,1,0)]]==4
shifts=Counter(L[idx[M(a)],idx[M(a)]]-L[idx[a],idx[a]] for a in pts)
assert shifts==Counter({-1:12,0:3,1:12})
x=s.Symbol('x')
poly=s.factor(Lcomplete.charpoly(x).as_expr())
expected=x*(x-12)**2*(x-10)**2*(x-9)**2*(x-8)**6*(x-6)**6*(x-5)**6*(x-3)*(x-1)
assert s.expand(poly-expected)==0
print('PASS Cube27 original 54 edges, preserved local only 18 (nine disconnected 3-site z chains)')
print('PASS minimal invariant extension 90 edges; 36 extra nonlocal: 12 length2 and 24 length3')
print('PASS [Lcube,PM] rank 24 / Frobenius norm squared 168')
print('PASS energy witness (1,0,0)->(1,1,0): 5J->4J, delta=-J')
print('PASS energy-shift counts: -1:12, zero:3, +1:12')
print('PASS invariant-completion Laplacian charpoly:',poly)
print('PHYSICS GATE: H=J Lcube, control of PM and measurable site states remain independent producers')

# Even Pin/O2 sign or U(1) local gauge dressing cannot repair an
# INCORRECT hopping support. Diagonal site gauge twists multiply each
# transformed nonzero bond by nonzero phases; they do not create
# the 36 missing native edges or delete the 36 new diagonal edges.
assert len(E.symmetric_difference(ME))==72
signs=s.diag(*((-1)**(i%2) for i in range(27)))
assert signs*signs==s.eye(27)
gauge_dressed=signs*P*L*P.T*signs
def support(A):
    return {canon(pts[i],pts[j]) for i in range(27)
            for j in range(i+1,27) if A[i,j]!=0}
assert support(gauge_dressed)==ME
assert len(support(gauge_dressed).symmetric_difference(support(L)))==72
print('PASS gauge-dressed modular permutation still mismatches 72 undirected cube bonds')
print('NO-GO no invertible sitewise U1/Pin phase factor can fix the underlying cube graph support')

# NOTATION: The illustrative lattice coupling J in some prose is a generic
# hopping strength kappa; it is NOT Klein's modular J(tau)=j(tau)-744.
