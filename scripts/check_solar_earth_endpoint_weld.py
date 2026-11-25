"""Exact abstract endpoint reachability/observability weld, not a plasma model.
Synthetic rational finite histories only. No physical actuation settings.
"""
import sympy as s
checks=0
def ck(p):
    global checks
    assert p
    checks+=1
# Donor RadioBio source-shaped four-parameter inverse: independent anchor.
h,j,e,p=s.symbols('h j e p', nonzero=True, real=True)
obs=s.Matrix([h*j,h*j*e,h*j*p]); J=obs.jacobian([h,j,e,p])
ck(J.rank()==3); ck(J*s.Matrix([h,-j,0,0])==s.zeros(3,1))
ck(s.factor(obs.col_join(s.Matrix([j])).jacobian([h,j,e,p]).det())==h**2*j**3)
# Signed finite history, including a hidden state and an invariant coordinate.
A=s.Matrix([[1,1,0,0],[0,1,1,0],[0,0,1,0],[0,0,0,1]])
B=s.Matrix([0,0,1,0]); O=s.Matrix([[1,0,0,0],[0,0,0,1]])
L=s.Matrix.hstack(A**2*B,A*B,B); C=O*L
ck(L.rank()==3); ck(C.rank()==1); ck(O*B==s.zeros(2,1))
ck(s.Matrix([[0,0,0,1]])*L==s.zeros(1,3))
# An exact endpoint can be reached even when its chosen full-state lift cannot.
# Weighted minimum input norm, not an assertion of physical paid energy.
W=s.diag(2,3,5); G=C*W.inv()*C.T; Gp=G.pinv()
y=s.Matrix([2,0]); u=W.inv()*C.T*Gp*y
ck(C*u==y); ck(u.T*W*u==y.T*Gp*y)
for z in C.nullspace(): ck((z.T*W*u)[0]==0)
v=s.Matrix(s.symbols('v:3',real=True)); q=C.nullspace()[0]*v[0]+C.nullspace()[1]*v[1]
ck(s.expand(((u+q).T*W*(u+q)-u.T*W*u-q.T*W*q)[0])==0)
# Full lift includes an unreachable invariant; output-target equivalence must
# be checked against the actual endpoint map, not arbitrary field distance.
P=s.Matrix([[1,0,0,0]])
xt=s.Matrix([2,0,0,7]); Cp=P*L; G2=Cp*W.inv()*Cp.T
u2=W.inv()*Cp.T*G2.inv()*P*xt
ck(P*L*u2==P*xt); ck(L.row_join(xt).rank()>L.rank())
# Objective observability iff ker M subset ker N (row-space inclusion).
M=s.Matrix([[1,0,0],[0,1,0]]); N=s.Matrix([[1,1,0]])
ck(N==N*M.pinv()*M); ck(all(N*z==s.zeros(1,1) for z in M.nullspace()))
Nbad=s.Matrix([[1,0,1]]); z=M.nullspace()[0]
ck(M*z==s.zeros(2,1) and Nbad*z!=s.zeros(1,1))
# Two source covariances with identical observations but unequal useful power.
S0=s.diag(1,1,0); S1=s.diag(1,1,1)
ck(M*S0*M.T==M*S1*M.T); ck(Nbad*S0*Nbad.T!=Nbad*S1*Nbad.T)
# A quadratic endpoint is identifiable from observations iff its Hermitian
# form factors through M (under unrestricted source vectors).
H=N.T*N; ck(H==M.T*(M.pinv().T*H*M.pinv())*M)
print(f'{checks}/{checks} exact checks PASS; SymPy {s.__version__}; min input norm squared { (u.T*W*u)[0] }; ranks {L.rank()}/{C.rank()}')
