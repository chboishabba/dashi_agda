"""Exact algebraic regressions, not native proof or PDE certificates."""
import sympy as S
from itertools import product
from fractions import Fraction as Q

# NS: same-output projected Fourier cells, reference rates and signed revision.
k=S.Matrix([1,1,0]); P=S.eye(3)-k*k.T/k.dot(k)
rows=[(S.Matrix([1,0,0]),S.Matrix([0,1,1]),S.Matrix([1,0,1])),
      (S.Matrix([0,1,0]),S.Matrix([1,0,S.I]),S.Matrix([0,-1,1])),
      (S.Matrix([1,0,1]),S.Matrix([1,1,-1]),S.Matrix([1,1,1]))]
N=[]
for p,u,v in rows:
    assert p.dot(u)==0 and (k-p).dot(v)==0
    N.append(P*(S.I*k.dot(u)*v))
g=lambda v,w:2*S.re(v.dot(w.conjugate()))
a=S.Rational(4); count=0
for i,j,s,sp in product(range(3),range(3),range(4),range(4)):
    K=lambda z:1/a-1/(a+z)
    assert S.simplify((K(sp)-K(s))*g(N[i],N[j])-(sp-s)*g(N[i],N[j])/((a+s)*(a+sp)))==0
    assert abs(K(sp)-K(s))<=abs(sp-s)/a**2
    count+=1
for rates in product(range(3),repeat=3):
    G=sum(g(N[i],N[j])/(a+rates[i]+rates[j]) for i,j in product(range(3),repeat=2))
    # Group by equal rates, preserve coherent cross terms.
    B={r:sum((N[i] for i in range(3) if rates[i]==r),S.zeros(3,1)) for r in set(rates)}
    assert S.simplify(G-sum(g(B[r],B[t])/(a+r+t) for r,t in product(B,repeat=2)))==0
    assert G>=0
    count+=1
v=N[0]; assert g(v,v)>0
assert sum(g(x,y) for x,y in product([v,-v],repeat=2))==0
assert sum(abs(g(x,y)) for x,y in product([v,-v],repeat=2))>0
count+=1
print('NS:',count,'signed revision / coherent reference fixtures')

# BSD: abstract p-adic vector-space dimension obstruction (not real curves).
count=0
for r,d in product(range(1,6),range(5)):
    L=S.Matrix([[1]+[0]*(r+d-1)])
    W=L[:,:r]
    assert W.rank()==1 and L.rank()==1
    assert len(L.nullspace())==r+d-1 and len(W.nullspace())==r-1
    count+=1
print('BSD:',count,'abstract local-observer dimension fixtures')

# Hodge: actual arithmetic of a totally real cubic field, not a K3 witness.
# x^3-3x+1, discriminant 81, three distinct real roots.
A=S.Matrix([[0,0,-1],[1,0,3],[0,1,0]])
Qm=S.Matrix(3,3,lambda i,j:S.trace(A**(i+j)))
assert A.charpoly().as_expr()==A.charpoly().gen**3-3*A.charpoly().gen+1
assert Qm.det()==81 and all(Qm[:i,:i].det()>0 for i in (1,2,3))
assert A.T*Qm==Qm*A
I=S.eye(3); C=(I+A*A).inv()
R=(I-A*A)*C; B=2*A*C
U=R.row_join(B).col_join(B.row_join(-R))
Q2=S.diag(Qm,Qm)
assert U*U==S.eye(6)
assert U.T*Q2*U==Q2
assert B*(I+R).inv()==A
print('Hodge: 6 exact cubic-field doubled-isometry identities')

# RH: exact divisor ratio source compression and early exceptional record.
NMAX=5040
sig=[0]*(NMAX+1)
for d in range(1,NMAX+1):
    for n in range(d,NMAX+1,d): sig[n]+=d
primes=list(S.primerange(1,NMAX+1))
count=0
for n in range(1,NMAX+1):
    exps=sorted(S.factorint(n).values(),reverse=True)
    m=int(S.prod(p**a for p,a in zip(primes,exps)))
    assert m<=n and sig[m]*n>=sig[n]*m
    count+=1
record=max(range(1,NMAX+1),key=lambda n:Q(sig[n],n))
assert record==5040 and Q(sig[record],record)==Q(403,105)
print('RH:',count,'exact source compression fixtures + 1 boundary record')
