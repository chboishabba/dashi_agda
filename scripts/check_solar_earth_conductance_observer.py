"""Conditional observational conductance bounds; no atmosphere/control fit.
Usage: python check.py. All profiles are dimensionless rational fixtures.
"""
import json
import sympy as s
R=s.Rational
# Reuse classical weighted Gram identity (existing Luo finite Cauchy owner).
# Q = n^T A n on common observed support, A positive diagonal;
# C = K n, where K holds declared fixed observation weights.
A=s.diag(2,3,5,7)
K=s.Matrix([[1,2,1,3],[2,-1,3,1]])
G=K*A.inv()*K.T
assert G.is_positive_definite
P=A.inv()*K.T*G.inv()*K
assert P*P==P and P.T*A==A*P and K*P==K
# Exact BIDI: least weighted norm lift, signed residual and Gram defect.
n=s.Matrix(s.symbols('n:4',real=True));c=K*n;z=P*n;r=n-z
assert K*r==s.zeros(2,1)
assert s.expand((z.T*A*r)[0])==0
assert s.expand((n.T*A*n-c.T*G.inv()*c-r.T*A*r)[0])==0
# Observed entries restrict the remaining norm, not silently fill the profile.
B=K[:,1:]; D=A[1:,1:]; Gm=B*D.inv()*B.T
assert Gm.is_positive_definite
v=s.Matrix([1,2,3,4]); q=(v.T*A*v)[0]; cv=K*v
qrem=q-A[0,0]*v[0]**2; crem=cv-K[:,0]*v[0]
assert qrem-(crem.T*Gm.inv()*crem)[0]>=0
# Two positive profiles: identical squared norm, distinct consumers.
a=s.Matrix([5,5]);b=s.Matrix([1,7]);assert a.dot(a)==b.dot(b)==50 and sum(a)!=sum(b)
# Exact upper bound over signed profiles is valid (possibly loose) for n>=0.
# Equality witness for single positive row and positive diagonal A.
k=K[0,:];p=A.inv()*k.T
assert all(x>0 for x in p)
assert (k*p)[0]**2==(p.T*A*p)[0]*(k*A.inv()*k.T)[0]
# Common steady recombination coefficient: production sums, not densities.
alpha=s.symbols('alpha',positive=True);qe,qi,qu=s.symbols('qe qi qu',nonnegative=True)
assert s.simplify((s.sqrt((qe+qi+qu)/alpha))**2-(qe+qi+qu)/alpha)==0
# Under same coefficient/shape, root-sum-square rather than arithmetic addition.
assert s.sqrt(9+16)==5 and s.sqrt(9)+s.sqrt(16)==7
print(json.dumps(dict(status='CONDITIONAL_CONDUCTANCE_OBSERVATION_GRAM',sympy=s.__version__,fixture=dict(Q=str(q),C=list(map(str,cv)),gram=[[str(x) for x in row] for row in G.tolist()],min_energy=str((cv.T*G.inv()*cv)[0]),residual_energy=str(q-(cv.T*G.inv()*cv)[0]),partial_Q=str(qrem),partial_min_energy=str((crem.T*Gm.inv()*crem)[0])),physical_admission=False,raw_radar_replayed=False),indent=2))
