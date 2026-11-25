import sympy as s
# Abstract power-normalized modal map; no environmental actuator parameters.
T=s.diag(s.Rational(1,2),1,s.Rational(1,4))
C=s.diag(4,1,0)
Q=T*C*T.H
assert Q==s.diag(1,1,0)
# Coherence counterexample: equal field norms, opposite covariance overlap.
C=s.Matrix([[1,1],[1,1]])/2
p=s.Matrix([1,1])/s.sqrt(2); m=s.Matrix([1,-1])/s.sqrt(2)
assert (p.H*C*p)[0]==1 and (m.H*C*m)[0]==0
# Unreachable desired state: weighted projection onto abstract actuator image.
B=s.Matrix([[1,0],[0,1],[0,0]]); G=s.diag(2,3,5); d=s.Matrix([2,-1,4])
u=(B.T*G*B).inv()*B.T*G*d
r=d-B*u
assert B.T*G*r==s.zeros(2,1) and (r.T*G*r)[0]==80
v=s.Matrix(s.symbols('v:2',real=True)); delta=d-B*v
assert s.expand((delta.T*G*delta-r.T*G*r-(v-u).T*B.T*G*B*(v-u))[0])==0
# Same natural absorption does not imply useful collection.
assert 10-8-1==1 and 10-3-2==5
print('abstract exact checks PASS; SymPy',s.__version__)
