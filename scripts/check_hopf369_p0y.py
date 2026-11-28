"""Exact primal/dual material-current weld on the original 27-node cube."""
import sympy as s
from itertools import product
R=s.Rational
# 1D primal hats integrated against normalized dual-cell densities.
T=s.Matrix([[R(3,4),R(1,8),0],[R(1,4),R(3,4),R(1,4)],[0,R(1,8),R(3,4)]])
# RT0 component basis: unit signed flux at dual faces -1,-1/2,1/2,1.
# Integral over primal edges [-1,0] and [0,1].
L=s.Matrix([[R(1,4),R(5,8),R(1,8),0],[0,R(1,8),R(5,8),R(1,4)]])
D=s.Matrix([[-1,1,0],[0,-1,1]])
H=s.Matrix([[1,-1,0,0],[0,1,-1,0],[0,0,1,-1]])
B=s.Matrix([[-1,0,0,0],[0,0,0,0],[0,0,0,1]])
assert D.T*L-B==T*H
assert s.ones(1,3)*T==s.ones(1,3)
assert T.det()!=0
P=list(product(range(3),repeat=3)); edges=[]; flux=[]
for a in range(3):
    for k in range(2):
        for tr in product(range(3),repeat=2):
            p=list(tr);p.insert(a,k);edges.append((a,tuple(p)))
    for k in range(4):
        for tr in product(range(3),repeat=2):
            p=list(tr);p.insert(a,k);flux.append((a,tuple(p)))
Q=s.kronecker_product(T,T,T)
G=s.zeros(27,54); J=s.zeros(54,108); E=s.zeros(27,108); V=s.zeros(27,108)
for i,(a,p) in enumerate(edges):
    q=list(p);q[a]+=1;G[P.index(p),i]=-1;G[P.index(tuple(q)),i]=1
for k,(a,p) in enumerate(flux):
    # Outward physical orientation on negative exterior face, +axis elsewhere.
    sign=-1 if p[a]==0 else 1
    for i,(b,q) in enumerate(edges):
        if b==a:J[i,k]=sign*L[q[a],p[a]]*s.prod(T[q[j],p[j]] for j in range(3) if j!=a)
    for i,q in enumerate(P):
        E[i,k]=sign*B[q[a],p[a]]*s.prod(T[q[j],p[j]] for j in range(3) if j!=a)
        V[i,k]=sign*H[q[a],p[a]]*s.prod(int(q[j]==p[j]) for j in range(3) if j!=a)
assert G*J-E==Q*V
assert Q.det()!=0
assert s.ones(1,27)*Q==s.ones(1,27)
# 9 dual patches on each face -> 4 primal face integrals.
F=s.Matrix([[1,R(1,2),0],[0,R(1,2),1]])
Rface=s.kronecker_product(F,F)
assert Rface.rank()==4 and len(Rface.nullspace())==5
assert s.ones(1,4)*Rface==s.ones(1,9)
# BIDI section and complete signed complement, not aggregate-only recovery.
S=Rface.T*(Rface*Rface.T).inv(); K=s.eye(9)-S*Rface
assert Rface*S==s.eye(4) and Rface*K==s.zeros(4,9) and S*Rface+K==s.eye(9)
assert K.rank()==5
assert s.diag(*([Rface]*6)).rank()==24
# Exact work and continuity for a nontrivial signed flux/voltage instance.
i=s.Matrix([(k%13)-6 for k in range(108)]); e=s.Matrix([(k%7)-3 for k in range(54)])
assert (e.T*J*i)[0]==((J.T*e).T*i)[0]
assert Q*V*i==G*J*i-E*i
# Potential/charge adjoint includes boundary term, even at zero net flux.
phi=s.Matrix([k%5-2 for k in range(27)])
assert (phi.T*Q*V*i)[0]==((J.T*G.T*phi-E.T*phi).T*i)[0]
# Same boundary face totals can have different nodal weak flux.
k=Rface.nullspace()[0];assert Rface*k==s.zeros(4,1) and s.kronecker_product(T,T)*k!=s.zeros(9,1)
print('PASS: exact 27x108 continuity, invertible 27-charge map, 54-to-24 boundary rank 24 + residual 30, work adjoint; SymPy',s.__version__)
