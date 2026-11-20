"""Exact finite moving-metric/SSPRK3 controls, not native production parity.

Donors: warp_stage_adjoint.py, warp_native_weighted_adjoint.py,
original Dashifine CMYK/alpha and DASHI/Quantum/TSVF.agda.
Physical state metric, renderer and source-control budget are distinct.
"""
import sympy as s

def weighted_reverse(M, W, V, lam):
    return W.inv()*M.T*V*lam

def reverse_ssprk3(A,B,C,p):
    l2=2*C.T*p/3
    l1=B.T*l2/4
    return p/3+3*l2/4+A.T*l1

def exact():
    I=s.eye(2)
    A=s.Matrix([[1,2],[0,1]])
    B=s.Matrix([[2,0],[3,1]])
    C=s.Matrix([[1,-1],[2,3]])
    M=I/3+2*C*(3*I/4+B*A/4)/3
    p=s.Matrix([2,-3])
    assert M.T*p==reverse_ssprk3(A,B,C,p)
    W=s.diag(2,5); V=s.diag(7,3)
    x=s.Matrix([4,1]); lam=V.inv()*p
    adj=weighted_reverse(M,W,V,lam)
    assert lam.T*V*M*x==adj.T*W*x
    T=s.Matrix([[1,2],[0,1]])
    U=s.Matrix([[2,1],[1,1]])
    Wt=T.inv().T*W*T.inv()
    Vt=U.inv().T*V*U.inv()
    Mt=U*M*T.inv()
    assert weighted_reverse(Mt,Wt,Vt,U*lam)==T*adj
    r=[s.Matrix([1,2]),s.Matrix([-2,1]),s.Matrix([3,-1]),s.Matrix([-2,-2])]
    assert sum((p.T*z)[0] for z in r)==(p.T*sum(r,s.zeros(2,1)))[0]
    print("PASS 4 exact identities")

if __name__=="__main__":
    exact()
