#!/usr/bin/env python3
from fractions import Fraction as F
import runpy

# Reuse the exact-rational construction and then verify the adjoint action of
# tri(O) on the three Peirce 8-spaces is literally the three triality modules:
#
#   X : conjugation o A o conjugation,
#   Y : B,
#   Z : C.

ns=runpy.run_path('scripts/check_rational_albert_triality_derivation_decomposition.py')
TB=ns['TB']; pairs=ns['pairs']; skew_matrix=ns['skew_matrix']; conj_twist=ns['conj_twist']
blockD=ns['blockD']; comm=ns['comm']; L=ns['L']; flat=ns['flat']; rank=ns['rank']

triABC=[]; triD=[]
for t in TB:
    A=skew_matrix(t,0); B=skew_matrix(t,28); C=skew_matrix(t,56)
    triABC.append((A,B,C)); triD.append(blockD((conj_twist(A),B,C)))

peirceX=[comm(L[1],L[i]) for i in range(3,11)]
peirceY=[comm(L[2],L[i]) for i in range(11,19)]
peirceZ=[comm(L[0],L[i]) for i in range(19,27)]

def coord_solver(basis):
    vecs=[flat(M) for M in basis]
    rows=[]; inds=[]; r0=0
    for idx in range(729):
        row=[v[idx] for v in vecs]
        rr=rank(rows+[row])
        if rr>r0:
            rows.append(row); inds.append(idx); r0=rr
            if rr==8: break
    assert r0==8
    def solve(M):
        b=[flat(M)[i] for i in inds]
        aug=[list(rows[i])+[b[i]] for i in range(8)]
        for c in range(8):
            p=next(r for r in range(c,8) if aug[r][c])
            aug[c],aug[p]=aug[p],aug[c]
            z=aug[c][c]; aug[c]=[x/z for x in aug[c]]
            for r in range(8):
                if r!=c and aug[r][c]:
                    z=aug[r][c]; aug[r]=[aug[r][j]-z*aug[c][j] for j in range(9)]
        coeff=[aug[i][-1] for i in range(8)]
        assert tuple(sum(coeff[j]*vecs[j][k] for j in range(8)) for k in range(729))==flat(M)
        return coeff
    return solve

solvers=[coord_solver(peirceX),coord_solver(peirceY),coord_solver(peirceZ)]
families=[peirceX,peirceY,peirceZ]

def module_matrix(D,fam,solve):
    cols=[solve(comm(D,P)) for P in fam]
    return [[cols[j][i] for j in range(8)] for i in range(8)]

for t,(D,(A,B,C)) in enumerate(zip(triD,triABC)):
    MX=module_matrix(D,peirceX,solvers[0])
    MY=module_matrix(D,peirceY,solvers[1])
    MZ=module_matrix(D,peirceZ,solvers[2])
    assert MX==conj_twist(A)
    assert MY==B
    assert MZ==C

print('triality basis elements checked:',len(TB))
print('X Peirce action = conjugation o A o conjugation')
print('Y Peirce action = B')
print('Z Peirce action = C')
print('PASS: exact three-module triality intertwining')
