from collections import Counter
import sympy as s
L=13
# Exact literal flat Eq120 axial support, before periodic identification.
w=Counter(x+j for x in range(-6,7) for j in range(L))
assert sum(w.values())==L**2
assert len(w)==25
# An off-axis fine link in the centered transverse box, axial coordinate 0.
# Straight center path derivative is zero; actual averaging coefficient is 7/L^5.
assert s.Rational(w[0],L**5)==s.Rational(7,L**5)
# On the one-block periodic carrier, both axial aliases combine.
assert sum(w[k] for k in w if k%L==0)==L
assert s.Rational(L,L**5)==s.Rational(1,28561)
for m in (1,2,3,4,5,13):
 A=s.zeros(m,m*L)
 for i in range(m):
  for k,v in w.items(): A[i,(i*L+k)%(m*L)]+=v
 T=s.zeros(m)
 for i in range(m):T[i,(i+1)%m]=1
 assert A*A.T==1469*s.eye(m)+364*(T+T.T)
 assert all(sum(A[:,j])==L for j in range(m*L))
 # Exact cyclic Gram floor as sum of squares, avoiding eigenvalue numerics.
 assert A*A.T-741*s.eye(m)==364*(s.eye(m)+T)*(s.eye(m)+T.T)
 # Each nonzero row belongs to at most two longitudinal coarse blocks.
 assert max(sum(A[i,j]!=0 for i in range(m)) for j in range(m*L))<=2
print('PASS 6 cyclic geometries; exact Gram SOS, overlap, and off-center straight/average derivative separation')
