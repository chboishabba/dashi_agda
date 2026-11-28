"""Exact mixed curve/K3 lower-product and middle-star controls.
Rank-six hyperbolic chart is a split model, not an actual algebraic cycle.
"""
import sympy as s
from itertools import product, combinations
checks=0
def ck(ok):
    global checks
    if not ok: raise AssertionError('mixed middle exterior guard failed')
    checks+=1
# Each K3 slot has target degree 2, each curve slot target degree 1.
# Assign slots to positive codimension factors; parity forces the two
# curve slots together. Every other factor is pure primitive K3 slots.
for k in (2,3):
    admissible=0
    for m in range(2,k+2):
        for addr in product(range(m),repeat=k+2):
            if set(addr)!=set(range(m)):continue
            degrees=[sum(2 if i<k else 1 for i in range(k+2) if addr[i]==j) for j in range(m)]
            if any(d%2 for d in degrees):continue
            admissible+=1
            ck(addr[k]==addr[k+1])
            pure=[sum(addr[i]==j for i in range(k)) for j in range(m) if j!=addr[k]]
            ck(pure and all(0<x<=k for x in pure))
            ck(any(x%2 or x==2 for x in pure))
    print('primitive slots',k,'decomposable admissible placements',admissible)
# Newton identities via roots, preserving all decomposable terms.
c1,c2,c3,c4=s.symbols('c1 c2 c3 c4'); e=[1,c1,c2,c3,c4]; p=[0]
for n in range(1,5):
    p.append(s.expand(sum((-1)**(j-1)*e[j]*p[n-j] for j in range(1,n))+(-1)**(n-1)*n*e[n]))
ck(p[3].subs({c1:0,c2:0})/6==c3/2)
ck(p[4].subs({c1:0,c2:0,c3:0})/24==-c4/6)
# Split rank-six wedge^3. Hyperbolic form pairs axes i and i+3.
I=list(combinations(range(6),3)); d=len(I); B=s.zeros(6)
for i in range(3):B[i,i+3]=B[i+3,i]=1
Q=s.Matrix(d,d,lambda i,j:B.extract(I[i],I[j]).det())
def sign(t):return (-1)**sum(t[i]>t[j] for i in range(len(t)) for j in range(i+1,len(t)))
W=s.Matrix(d,d,lambda i,j:sign(I[i]+I[j]) if not set(I[i])&set(I[j]) else 0)
# q(Jx,y)=wedge(x,y), hence J^T Q=W.
J=(W*Q.inv()).T
ck(J*J==s.eye(d)); ck(J.T*Q==-Q*J); ck(s.trace(J)==0)
for eps in (-1,1):
    P=(s.eye(d)+eps*J)/2
    ck(P*P==P);ck(P.rank()==10)
    # Tensor associated to operator P using inverse source metric;
    # full wedge contraction kills identity, retains the signed star.
    tensor=P*Q.inv()
    vol=sum(tensor[i,j]*W[i,j] for i in range(d) for j in range(d))
    ck(vol==eps*10)
    print('chirality',eps,'orientation contraction',vol)
ck(sum(Q.inv()[i,j]*W[i,j] for i in range(d) for j in range(d))==0)
print(f'{checks}/{checks} exact mixed-middle guards PASS')
