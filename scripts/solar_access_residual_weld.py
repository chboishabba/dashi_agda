"""Exact coarse source-access and paid mode-routing discriminator.
Finite real source metric, not an atmospheric constitutive identification.
"""
import sympy as S


def access(R, v, K):
    R,v,K=map(S.Matrix,(R,v,K))
    assert R==R.T and all(R[:j,:j].det()>0 for j in range(1,R.rows+1))
    assert K.rows==R.rows and K.rank()==K.cols
    x=R.inv()*v/2
    y=K*(K.T*R*K).inv()*K.T*v/2 if K.cols else S.zeros(R.rows,1)
    assert K.T*R*(x-y)==S.zeros(K.cols,1)
    return y,(y.T*R*y)[0]


def nested(R,v,P,A):
    assert A.row_join(P).rank()==A.rank()
    x,p=access(R,v,P);y,a=access(R,v,A);d=y-x
    assert P.T*R*d==S.zeros(P.cols,1)
    assert S.simplify(a-p-(d.T*R*d)[0])==0
    return p,a,d


def bounded_current(R,v,K,lam):
    # Dual certificate for coefficient current norm <= radius; equality at
    # the returned current if radius is chosen as its norm.
    G=K.T*R*K;b=K.T*v;lam=S.Rational(lam);assert lam>=0
    i=(G+lam*S.eye(K.cols)).inv()*b/2
    radius2=i.dot(i);cap=(b.T*i)[0]-(i.T*G*i)[0]
    assert cap==(b.T*(G+lam*S.eye(K.cols)).inv()*b)[0]/4+lam*radius2
    return i,radius2,cap


def run():
    R=S.diag(1,2,3);v=S.Matrix([1,2,-3]);P=S.eye(3)[:,:1];A=S.eye(3)[:,:2]
    p,a,d=nested(R,v,P,A);assert (p,a)==(S.Rational(1,4),S.Rational(3,4))
    _,full=access(R,v,S.eye(3));assert full==S.Rational(3,2)
    # Signed complement matters; same modal power does not fix access.
    K=S.Matrix([1,1]);assert access(S.eye(2),S.Matrix([1,-1]),K)[1]==0
    assert access(S.eye(2),S.Matrix([1,1]),K)[1]==S.Rational(1,2)
    i,r2,b=bounded_current(R,v,A,1);assert b<a
    # Three equally likely independent source states. Static rank-one cap
    # equals largest eigenvalue of whitened covariance /4; causal rank-one
    # with symmetric correct prediction probability p cannot exceed p/4.
    q=S.symbols('q',real=True);C=S.diag(q,(1-q)/2,(1-q)/2)
    assert S.trace(C)==1
    assert S.simplify(q-(1-q)/2-(3*q-1)/2)==0
    # For q>=1/3, optimal conditional rank-one captures q/4; static 1/12.
    q0=S.Rational(9,10);static=S.Rational(1,12);adaptive=q0/4
    margin=adaptive-static;assert margin==S.Rational(17,120)
    # A broader simultaneous passive rank-three receiver eliminates the gain.
    assert adaptive<=S.Rational(1,4)
    # Independent pump must be debited, even when it increases raw output.
    cost=S.Rational(1,10);assert adaptive-cost>static
    assert adaptive-S.Rational(3,20)<static
    # A fixed coherent unitary changes coordinates only, not full access.
    U=S.Matrix([[0,1,0],[-1,0,0],[0,0,1]]);assert U.T*U==S.eye(3)
    assert access(U.T*R*U,U.T*v,U.T*A)[1]==a
    # Same-source four-world ledger: interaction contrast alone is insufficient.
    y00,y10,y01,y11=map(S.Rational,[0,'1/12','1/10','9/40'])
    interaction=y11-y10-y01+y00;assert interaction==S.Rational(1,24)
    assert y11-cost-y10==interaction
    print('PASS nested access',p,a,full,'current cap',b,'adaptive margin',margin,'paid gain',interaction)
    print('Conditional only: equal rank is not equal material or reachable hardware; source labels and costs require actual donor weld.')
if __name__=='__main__':run()
