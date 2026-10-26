#!/usr/bin/env python3
"""Exact constructive reconciliation of native Cube27 and internal order-27 charge.
A complex 2-charge quantum fibre has U=diag(1,zeta_27), while the 27
spatial sites retain their ORIGINAL nearest-neighbour graph. This toy
is not an actual Monster VOA, KK gauge field, or measured physical system.
"""
from itertools import product
import sympy as s
sites=list(product((-1,0,1),repeat=3))
assert len(sites)==27
idx={p:i for i,p in enumerate(sites)}
L=s.zeros(27)
for a,i in idx.items():
    for b,j in idx.items():
        if sum(abs(x-y) for x,y in zip(a,b))==1:
            L[i,j]=-1
    L[i,i]=-sum(L[i,j] for j in range(27))
assert s.trace(L)==108
zeta=s.exp(2*s.pi*s.I/27)
Q=s.diag(1,zeta)
H=s.kronecker_product(L,s.eye(2))
U=s.kronecker_product(s.eye(27),Q)
assert H*U==U*H
assert s.simplify(Q**27-s.eye(2))==s.zeros(2)
assert all(zeta**k!=1 for k in range(1,27))
# Faithful order27 complex quantum charge acts on INTERNAL coherent
# neutral/charged reference, and does not permute 27 spatial sites.
Q19=s.diag(1,zeta**19)
assert Q19[0,0]==1 and Q19[1,1]!=1
prob=(2+zeta**19+zeta**(-19))/4
w=s.exp(s.pi*s.I/27)
assert s.expand(prob-(w**19+w**(-19))**2/4)==0
assert abs(complex(s.N(prob-s.cos(s.pi*19/27)**2)))<1e-14
assert 0<float(complex(s.N(prob)).real)<1
# Existing source-selected M acts on real x/y site coordinates;
# its spatial gate commutes with the internal charge gate, but not
# with the ORIGINAL nearest-neighbour spatial Hamiltonian.
res=lambda a:(a+1)%3-1
M=lambda p:(res(p[0]+p[1]),res(p[0]-p[1]),p[2])
PM=s.zeros(27)
for p,i in idx.items():PM[idx[M(p)],i]=1
gate=s.kronecker_product(PM,s.eye(2))
assert gate*U==U*gate
assert gate*H!=H*gate
edges={tuple(sorted((a,b))) for a in sites for b in sites
       if sum(abs(x-y) for x,y in zip(a,b))==1}
M_edges={tuple(sorted((M(a),M(b)))) for a,b in edges}
assert len(edges|M_edges)==90 and len(edges|M_edges)-len(edges)==36
print("PASS actual Cube27 remains original 54-edge geometry")
print("PASS internal faithful C27 U=I27 tensor diag(1,zeta27) commutes with spatial graph Hamiltonian")
print("PASS spatial M and internal charge commute, but spatial M breaks native cube adjacency dynamics")
print("PASS minimal M-invariant spatial completion adds 36 nonlocal edges")
print("PASS coherent two-charge phase contrast: Pplus(g^19)=",s.N(prob,12),"vs Pplus(identity)=1")
print("LIMIT a one-charge global phase is unobservable; two charge sectors/phase reference required")
print("LIMIT no Monster VOA, KK connection or AdS3 physical producer instantiated")
