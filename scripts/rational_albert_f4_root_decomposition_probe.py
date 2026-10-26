#!/usr/bin/env python3
"""Root-decomposition diagnostic for the literal rational Albert derivation algebra.

This is intentionally diagnostic authority.  It consumes the exact 52-dimensional
inner-derivation matrices from `rational_albert_g2_f4_probe.py`, chooses the
deterministic regular element H = sum((i+1) D_i), computes its 4-dimensional
centralizer, and numerically complexifies the adjoint representation.

Checks:
* centralizer(H) has dimension 4;
* ad(H) has 4 zero and 48 nonzero eigenvalues/root spaces;
* the 48 roots split into 24 short and 24 long roots;
* squared root lengths occur in ratio exactly 2 (numerically 1/18 and 1/9 in
  the chosen trace-form normalization);
* four roots can be selected with the standard F4 Cartan matrix.
"""

import runpy
import sympy as sp
import numpy as np

ns = runpy.run_path("scripts/rational_albert_g2_f4_probe.py")
INNER = ns["INNER"]
F = ns["F"]

_, pivots = F.rref()
basis = [INNER[i] for i in pivots]
assert len(basis) == 52

Bflat = sp.Matrix.hstack(*[D.reshape(729,1) for D in basis])
_, row_pivots = Bflat.T.rref()
rows = list(row_pivots)
M = Bflat[rows,:]
Minv = M.inv()

def coords(mat):
    v = mat.reshape(729,1)
    return Minv * v[rows,:]

ad = []
for A in basis:
    ad.append(sp.Matrix.hstack(*[coords(A*B-B*A) for B in basis]))

adH = sum(((i+1)*ad[i] for i in range(52)), sp.zeros(52))
cartan_vectors = adH.nullspace()
assert len(cartan_vectors) == 4
adC = [sum((v[i]*ad[i] for i in range(52)), sp.zeros(52)) for v in cartan_vectors]

A = np.array(adH.evalf(), dtype=float)
evals, evecs = np.linalg.eig(A)
zero = [i for i,z in enumerate(evals) if abs(z) < 1e-7]
assert len(zero) == 4

adC_np = [np.array(C.evalf(), dtype=float) for C in adC]
roots = []
for z,v in zip(evals,evecs.T):
    if abs(z) < 1e-7:
        continue
    vv = np.vdot(v,v)
    roots.append(np.array([np.vdot(v,C@v)/vv for C in adC_np]))
assert len(roots) == 48

K = np.array([[float(sp.trace(adC[i]*adC[j])) for j in range(4)] for i in range(4)])
Ki = np.linalg.inv(K)
def ip(a,b): return float((a @ Ki @ b).real)
lengths = np.array([ip(a,a) for a in roots])
short = [i for i,l in enumerate(lengths) if abs(l-1/18)<1e-6]
long = [i for i,l in enumerate(lengths) if abs(l-1/9)<1e-6]
assert len(short)==24 and len(long)==24

# Search a standard F4 simple system: long-long-short-short.
solution = None
for i0 in long:
  for i1 in long:
    if i1==i0 or abs(2*ip(roots[i0],roots[i1])/lengths[i0] + 1)>1e-5: continue
    for i2 in short:
      if abs(ip(roots[i0],roots[i2]))>1e-5: continue
      if abs(2*ip(roots[i1],roots[i2])/lengths[i1] + 1)>1e-5: continue
      if abs(2*ip(roots[i2],roots[i1])/lengths[i2] + 2)>1e-5: continue
      for i3 in short:
        if i3==i2: continue
        if abs(ip(roots[i0],roots[i3]))>1e-5 or abs(ip(roots[i1],roots[i3]))>1e-5: continue
        if abs(2*ip(roots[i2],roots[i3])/lengths[i2] + 1)>1e-5: continue
        if abs(2*ip(roots[i3],roots[i2])/lengths[i3] + 1)>1e-5: continue
        solution=(i0,i1,i2,i3); break
      if solution: break
    if solution: break
  if solution: break
assert solution is not None

C = np.zeros((4,4),dtype=int)
for i,ri in enumerate(solution):
    for j,rj in enumerate(solution):
        C[i,j] = round(2*ip(roots[ri],roots[rj])/lengths[ri])
expected=np.array([[2,-1,0,0],[-1,2,-1,0],[0,-2,2,-1],[0,0,-1,2]])
assert np.array_equal(C,expected)

print("cartan_dimension=4")
print("nonzero_root_spaces=48")
print("short_roots=24 long_roots=24")
print("root_length_squares=1/18,1/9 ratio=2")
print("simple_root_indices=",solution)
print("cartan_matrix=")
print(C)
