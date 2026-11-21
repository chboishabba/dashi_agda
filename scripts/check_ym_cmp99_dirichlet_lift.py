import sympy as s
# Exact finite scalar discriminator, not a full CMP99 physical domain.
D=s.zeros(6,6)
for i in range(6):
 D[i,i]=-1; D[i,(i+1)%6]=1
E=s.eye(6)[:,1:5]
L=E.T*D.T*D*E
assert L==(D*E).T*(D*E)
Di=D[1:4,1:5]
assert L-Di.T*Di==s.diag(1,0,0,1)
assert L.det()==5
# Complete disjoint blocks in selected carrier; unequal physical volumes.
Q=s.Matrix([[s.Rational(1,2),s.Rational(1,2),0,0],[0,0,1,0],[0,0,0,1]])
V=s.diag(2,1,1); Qs=Q.T*V
assert Q*Qs==s.eye(3)
a=s.Rational(2,3); B=s.diag(a/4,a,a)
G=(L+Qs*B*Q).inv()
W=Q*G; Ws=W.T*V
R=s.eye(4)-Ws*(W*Ws).inv()*W
assert R.T==R and R*R==R and W*R==s.zeros(3,4)
assert L*G*R==R
# Schur complement with source penalty subtraction, using a complete row map.
H=G*Qs*(Q*G*Qs).inv()
K=(Q*G*Qs).inv()-B
assert Q*H==s.eye(3)
assert H.T*L*H==V*K
assert (V*K).is_symmetric()
print('PASS: Dirichlet boundary energy, weighted projector and penalty-subtracted lift energy')
