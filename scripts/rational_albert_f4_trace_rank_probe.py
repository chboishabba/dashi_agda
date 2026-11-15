#!/usr/bin/env python3
"""Second-stage exact/numerical diagnostics for the rational Albert derivation algebra.

Consumes the literal matrices built by `rational_albert_g2_f4_probe.py` and checks
features relevant to identifying the real scalar extension as compact type F4:

* choose an exact 52-element basis from the 351 inner derivations;
* `-tr(D_i D_j)` has full rank 52;
* exact LDL diagonal entries are positive (only 3/2 and 6);
* the Lie-algebra center is zero;
* the deterministic element H=sum((i+1)D_i) has centralizer dimension 4
  (the last rank is a floating numerical diagnostic; all preceding checks are exact).
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

G = sp.Matrix([[-sp.trace(A*B) for B in basis] for A in basis])
assert G.rank() == 52
_, D = G.LDLdecomposition(hermitian=False)
diag = [sp.simplify(D[i,i]) for i in range(52)]
assert all(value > 0 for value in diag)
assert set(diag) <= {sp.Rational(3,2), sp.Integer(6)}

# Exact center computation in the 52-dimensional basis.
center_columns = []
for A in basis:
    blocks = []
    for B in basis:
        blocks.extend(list((A*B-B*A).reshape(729,1)))
    center_columns.append(sp.Matrix(blocks))
center_matrix = sp.Matrix.hstack(*center_columns)
assert 52 - center_matrix.rank() == 0

# Deterministic regular-element centralizer diagnostic.
H = sum(((i+1)*A for i,A in enumerate(basis)), sp.zeros(27))
C = np.column_stack([
    np.array(A*H-H*A, dtype=float).reshape(-1) for A in basis
])
regular_centralizer_dimension = 52 - np.linalg.matrix_rank(C, tol=1e-9)
assert regular_centralizer_dimension == 4

print("derivation_basis=52")
print("negative_trace_form_rank=52")
print("negative_trace_ldl_values=3/2,6 only")
print("center_dimension=0")
print("regular_centralizer_dimension=4")
