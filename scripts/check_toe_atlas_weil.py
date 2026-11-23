"""Exact selected ATLAS D4 lift on the paired Schrödinger model."""
from check_toe_atlas_mirror import np, sp, Pa, inv, r, m, eq, Js, Coc, rank
from itertools import product
def eq(a,b): return bool(np.all((a-b)%3==0))
A=inv(Pa)@r@Pa%3
U=A[:6,6:]; V=A[6:,:6]
assert eq(A[:6,:6],0) and eq(A[6:,6:],0)
assert eq(U@V,-np.eye(6,dtype=int)) and eq(U,U.T) and eq(V,V.T)
assert eq(A.T@Js@A,Js)
E=(A.T@Coc@A-Coc)%3
assert eq(E,E.T)
X=np.array(list(product(range(3),repeat=6)),dtype=np.int64)
# Matrix row y, column x; entries zeta^(s*y^T V x)/27.
K=X@V@X.T%3
for phase in (1,2):
 for j in range(6):
  a=np.eye(6,dtype=int)[j]
  # T(a): kernel at x+a; M(Va): output phase.
  assert eq(phase*(X@V@(X+a).T-K),phase*(X@V@a)[:,None])
  # M(b): input phase; T(Ub): output index y-Ub.
  assert eq(phase*((X-U@a)@V@X.T-K),phase*(X@a)[None,:])
# Exact root sums by coefficient counts, not floating-point complex arithmetic.
# Symmetry and nondegeneracy imply F^2 is parity and F*F=I.
for x in X:
 v=X@V@x%3
 counts=np.bincount(v,minlength=3)
 assert tuple(counts)==((729,0,0) if not x.any() else (243,243,243))
assert eq(K,K.T)
# For the asymmetric cocycle lift q(a,b)=-a.b in this off-diagonal chart.
for x in np.vstack((np.zeros((1,12),dtype=int),np.eye(12,dtype=int),np.ones((1,12),dtype=int))):
 assert (2*x@E@x+x[:6]@x[6:])%3==0
assert eq(E,np.block([[np.zeros((6,6),dtype=int),-np.eye(6,dtype=int)],[-np.eye(6,dtype=int),np.zeros((6,6),dtype=int)]]))
print('U =',U.tolist());print('V =',V.tolist())
print('PASS: 2 phases, 12 Weyl generator squares each, all 729^2 entries; 729 exact root sums; D4 Fourier square and conjugate inverse')
