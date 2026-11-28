import sympy as s
from itertools import combinations,combinations_with_replacement
from check_hopf369_br204_boost_null import run
I=range(5); P=list(combinations(I,2)); Q=list(combinations_with_replacement(range(10),2)); eta=[-1,1,1,1,1]
q=s.symbols('q:55'); m=s.Matrix(10,10,lambda a,b:q[Q.index(tuple(sorted((a,b))))])
def W(a,b,c,d):
    if a==b or c==d:return s.S.Zero
    return (1 if a<b else -1)*(1 if c<d else -1)*m[P.index(tuple(sorted((a,b)))),P.index(tuple(sorted((c,d))))]
cons=[W(a,b,c,d)+W(a,c,d,b)+W(a,d,b,c) for a,b,c,d in combinations(I,4)]
cons.extend(sum(eta[a]*W(a,b,a,d) for a in I) for b,d in combinations_with_replacement(I,2))
C=s.Matrix(cons).jacobian(q); V=s.Matrix.hstack(*C.nullspace()); X=s.Matrix(list(m)).jacobian(q)*V; G=X.T*X
A=[]
for i in range(1,5):
    L=s.zeros(10)
    for k in range(1,5):
        if k==i:continue
        e=P.index((0,k)); b=P.index(tuple(sorted((i,k)))); L[e,b]=L[b,e]=1 if i<k else -1
    A.append(G.inv()*X.T*s.kronecker_product(L,s.eye(10))*X)
run(X,G,A)
