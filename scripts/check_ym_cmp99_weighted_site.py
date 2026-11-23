import sympy as s
# Exact weighted nested disjoint site blocks, rational adjoint rotations.
I=s.eye(3); t=s.Rational(1,7); a=(1-t*t)/(1+t*t); b=2*t/(1+t*t)
T=s.Matrix([[1,0,0],[0,a*a-b*b,-2*a*b],[0,2*a*b,a*a-b*b]])
assert T.T*T==I
F=s.diag(*([I]*4)); M=2*s.eye(6); O=4*I
Q=s.BlockMatrix([[I,T,s.zeros(3),s.zeros(3)],[s.zeros(3),s.zeros(3),T,I]]).as_explicit()/2
P=s.BlockMatrix([[T,I]]).as_explicit()/2
adj=lambda A,X,Y:X.inv()*A.T*Y
Qs=adj(Q,F,M); Ps=adj(P,M,O)
assert Q*Qs==s.eye(6) and P*Ps==I
K=P*Q; Ks=adj(K,F,O)
assert Ks==Qs*Ps and K*Ks==I
assert (Ks*K)**2==Ks*K
# Mixed-level disjoint cover: first two fine sites averaged, last two kept.
J=s.BlockMatrix([[I/2,T/2,s.zeros(3),s.zeros(3)],[s.zeros(3),s.zeros(3),I,s.zeros(3)],[s.zeros(3),s.zeros(3),s.zeros(3),I]]).as_explicit()
V=s.diag(2*I,I,I); Js=adj(J,F,V)
assert J*Js==s.eye(9)
# Truncating an input without changing the coarse measure breaks coisometry.
E=s.eye(12)[:,:9]; B=J*E; Bstar=adj(B,s.eye(9),V)
assert B*Bstar!=s.eye(9)
# CMP99 (3.24) penalty exponents, not site Hilbert metric.
L=s.Integer(13); eta=s.Rational(1,169); alpha=s.Rational(5,7); aj=alpha
for j in range(1,6):
    assert s.factor(1/aj-sum(L**(-2*k)/alpha for k in range(j)))==0
    ell=L**j*eta
    assert ell**2 * (aj*ell**2) == aj*ell**4
    aj=alpha*aj/(alpha/L**2+aj)
print('PASS: weighted one-step and composition, mixed disjoint cover, boundary negative control, five penalty recurrence checks')
