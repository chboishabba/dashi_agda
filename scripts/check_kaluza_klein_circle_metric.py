#!/usr/bin/env python3
"""Exact algebraic KK metric check in a 2+1 representative block; not Einstein-Maxwell."""
import sympy as s

def main():
    g00,g01,g11,phi,k=s.symbols("g00 g01 g11 phi k",nonzero=True)
    a,b,u,v=s.symbols("a b u v")
    g=s.Matrix([[g00,g01],[g01,g11]])
    A=s.Matrix([a,b]); dchi=s.Matrix([u,v])
    def kk(A):
        w=k*A
        return g.row_join(phi**2*w).col_join(
            (phi**2*w).T.row_join(s.Matrix([[phi**2]]))
        )+s.diag(0,0,0)+s.Matrix.vstack(
            s.Matrix.hstack(phi**2*w*w.T,s.zeros(2,1)),
            s.zeros(1,3))
    J=s.eye(3)
    J[2,0]=-k*u;J[2,1]=-k*v
    M=kk(A);Mnew=kk(A+dchi)
    assert all(s.simplify(z)==0 for z in M-J.T*Mnew*J)
    assert s.factor(M.det()-phi**2*g.det())==0
    inv=s.eye(3)
    inv[:2,:2]=g.inv()
    inv[:2,2]=-k*g.inv()*A
    inv[2,:2]=-k*A.T*g.inv()
    inv[2,2]=phi**-2+k**2*(A.T*g.inv()*A)[0]
    assert all(s.simplify(z)==0 for z in M*inv-s.eye(3))
    print("PASS exact symbolic: KK gauge covariance, determinant and inverse")
    print("LIMIT: 2+1 toy base; no 4+1 curvature/Einstein-Maxwell theorem")

if __name__=="__main__":
    main()
