#!/usr/bin/env python3
"""BR27/28: physical Weyl--Israel superenergy and exact characteristic carrier.
All signed jumps use plus=n=0, minus=n=L, j=-6/5. Classical identities;
projected Bianchi evolution is not yet a constraint propagation theorem.
"""
import sympy as s
from itertools import combinations, combinations_with_replacement, product

I=range(5); P=list(combinations(I,2)); Q=list(combinations_with_replacement(range(10),2))
eta=[-1,1,1,1,1]; h=s.diag(-1,1,1,1)
q=s.symbols('q:55')

def read(m,a,b,c,d):
    if a==b or c==d:return s.S.Zero
    return (1 if a<b else -1)*(1 if c<d else -1)*m[P.index(tuple(sorted((a,b)))),P.index(tuple(sorted((c,d))))]

def carrier():
    m=s.Matrix(10,10,lambda a,b:q[Q.index(tuple(sorted((a,b))))])
    W=lambda a,b,c,d:read(m,a,b,c,d)
    cons=[W(a,b,c,d)+W(a,c,d,b)+W(a,d,b,c) for a,b,c,d in combinations(I,4)]
    cons.extend(sum(eta[a]*W(a,b,a,d) for a in I) for b,d in combinations_with_replacement(I,2))
    C=s.Matrix(cons).jacobian(q); V=s.Matrix.hstack(*C.nullspace())
    # Embedding into all ordered first/second bivector components (100 entries).
    X=s.Matrix(list(m)).jacobian(q)*V; G=X.T*X
    # wall tracefree symmetric M, positive norm on all 16 ordered entries
    keys=[p for p in combinations_with_replacement(range(4),2) if p!=(0,0)]
    mp=s.symbols('m:9')
    M=s.Matrix(4,4,lambda a,b:mp[keys.index(tuple(sorted((a,b))))] if a or b else 0)
    M[0,0]=sum(M[i,i] for i in range(1,4)); Y=s.Matrix(list(M)).jacobian(mp); H=Y.T*Y
    def jump(a,b,c,d):
        if 4 not in (a,b,c,d):return -(h[a,c]*M[b,d]+M[a,c]*h[b,d]-h[a,d]*M[b,c]-M[a,d]*h[b,c])
        if (4 in (a,b))!=(4 in (c,d)):return s.S.Zero
        return 2*M[a,c] # packed increasing pairs, normal last
    J=s.Matrix([jump(*P[a],*P[b]) for a,b in Q]).jacobian(mp)
    assert V.cols==35 and J.rank()==9 and C*J==s.zeros(C.rows,9)
    J0=V.gauss_jordan_solve(J)[0]
    # Positive Maxwell evolution matrices (sign w_t=A^i w_i).
    bulk=[]; wall=[]
    for i in range(1,5):
        L=s.zeros(10)
        for k in range(1,5):
            if k==i:continue
            e=P.index((0,k)); b=P.index(tuple(sorted((i,k))))
            L[e,b]=L[b,e]=1 if i<k else -1
        bulk.append(G.inv()*X.T*s.kronecker_product(L,s.eye(10))*X)
        if i<4:
            Lw=s.zeros(16)
            for a in range(4):Lw[4*a,4*a+i]=Lw[4*a+i,4*a]=1
            wall.append(H.inv()*Y.T*Lw*Y)
    # Source term -C_{n a 0 i} in wall row a, column i; projection is
    # Euclidean orthogonal onto symmetric tracefree M.
    raw=s.Matrix([W(4,a,0,i) if i else 0 for a in range(4) for i in range(4)]).jacobian(q)*V
    R=H.inv()*Y.T*raw # M_t=...-R mean(W)
    return C,V,X,G,Y,H,J0,bulk,wall,R,W,m

def bel(m,a,b,c,d):
    W=lambda a,b,c,d:read(m,a,b,c,d)
    t=sum(eta[e]*eta[f]*(W(a,e,c,f)*W(b,e,d,f)+W(a,e,d,f)*W(b,e,c,f)) for e,f in product(I,repeat=2))
    if a==b:t-=s.Rational(1,2)*eta[a]*sum(eta[e]*eta[f]*eta[g]*W(e,f,c,g)*W(e,f,d,g) for e,f,g in product(I,repeat=3))
    if c==d:t-=s.Rational(1,2)*eta[c]*sum(eta[e]*eta[f]*eta[g]*W(a,e,f,g)*W(b,e,f,g) for e,f,g in product(I,repeat=3))
    if a==b and c==d:t+=s.Rational(1,8)*eta[a]*eta[c]*sum(eta[e]*eta[f]*eta[g]*eta[k]*W(e,f,g,k)**2 for e,f,g,k in product(I,repeat=4))
    return t

def run():
    C,V,X,G,Y,H,J,A,B,R,W,m=carrier()
    for a in A:assert G*a==(G*a).T
    for a in B:assert H*a==(H*a).T
    S=G*A[3]
    # independent packed normal flux, then exact signed Israel work identity
    F=sum(W(0,i,a,b)*W(4,i,a,b) for i in range(1,4) for a,b in P)
    assert S==V.T*s.hessian(F,q)*V
    assert S*J==3*R.T*H
    assert S.rank()==26 and (S*J).rank()==8
    assert A[3].eigenvals()=={-1:5,-s.Rational(1,2):8,0:9,s.Rational(1,2):8,1:5}
    assert B[0].eigenvals()=={-1:1,-s.Rational(1,2):2,0:3,s.Rational(1,2):2,1:1}
    ker=(S*J).nullspace(); assert len(ker)==1
    assert Y*ker[0]==s.Matrix(list(s.diag(3,1,1,1)))
    # Normal-reflection parity 19+16, full signed zero-speed kernel retained.
    par=s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in Q])
    assert len(((par-s.eye(55))*V).nullspace())==19
    assert len(((par+s.eye(55))*V).nullspace())==16
    # Exact spatial Maxwell constraint principal symbol, k along n.
    bad=[(0,4),*list(combinations(range(1,4),2))]
    D=s.Matrix([W(a,b,c,d) for a,b in bad for c,d in P]).jacobian(q)*V
    K=s.Matrix.hstack(*D.nullspace())
    assert D.rank()==25 and D*A[3]*K==s.zeros(D.rows,10)
    assert K.gauss_jordan_solve(A[3]*K)[0].eigenvals()=={-1:5,1:5}
    # Rational independent full Bel tensor contraction and exchange symmetry.
    vals=V*s.Matrix([s.Rational((i*i+3*i)%17-8,7) for i in range(35)])
    mm=m.subs(dict(zip(q,vals)))
    energy=sum(x*x for x in mm)/2
    assert bel(mm,0,0,0,0)==energy and energy>0
    for i in range(1,5):
        flux=sum(read(mm,0,k,a,b)*read(mm,i,k,a,b) for k in range(1,5) if k!=i for a,b in P)
        assert bel(mm,i,0,0,0)==flux and bel(mm,0,0,i,0)==flux
        assert bel(mm,0,i,0,0)==flux
    # Full wall superenergy contraction (independent formula) on a tracefree M.
    M=s.Matrix(4,4,list(Y*s.Matrix([s.Rational(i-4,3) for i in range(9)])))
    def wallS(a,b,c,d):
        return (M[a,c]*M[b,d]+M[a,d]*M[b,c]-h[a,b]*(M*h*M)[c,d]-h[c,d]*(M*h*M)[a,b]+h[a,b]*h[c,d]*s.trace(h*M*h*M)/2)
    assert wallS(0,0,0,0)==sum(x*x for x in M)/2
    for i in range(1,4):
        assert wallS(i,0,0,0)==sum(M[0,k]*M[i,k] for k in range(4))
        assert wallS(i,0,0,0)==wallS(0,0,i,0)
    # Static boost cancellation in J_B=B^a_bcd T^b T^c T^d:
    # first pair symmetric, last-pair terms cancel by pair exchange.
    for i in range(1,5):assert bel(mm,i,0,0,0)-bel(mm,0,0,i,0)==0
    j=-s.Rational(6,5); assert -3*j==s.Rational(18,5)>0
    print('PASS exact 35-component Weyl carrier, 9-component wall, Bel flux and positive work coefficient')
    print('bulk normal speeds: +/-1 x5, +/-1/2 x8, zero x9; wall tangential speeds +/-1 x1, +/-1/2 x2, zero x3')
    print('PASS active transmission rank 26, jump coupling rank 8, physical flat spatial constraint kernel 10')

if __name__=='__main__':run()
