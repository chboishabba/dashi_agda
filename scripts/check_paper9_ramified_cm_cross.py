#!/usr/bin/env python3
"""Ramification-indexed CM cross replay: reuse original integer slice producers.

The two additional cases are classical elliptic points, not physical
calibration. This verifies finite coefficients and exact rational branch
geometry; analytic source attachment and kernel acceptance are separate.
"""
from math import gcd
from sympy import Matrix, I, sqrt, simplify, expand, symbols, Rational, rem
from check_cm163_modular_diagonal import diagonal
from check_cm163_derivative_slice import slice_poly

def main():
    for p, K, e, z, M, expected_trace, expected_k in [
        (5, 1728, 2, I, Matrix([[2,-1],[1,2]]),
         -Rational(14,25), Rational(23,46656)),
        (7, 0, 3, (-1+I*sqrt(3))/2, Matrix([[2,-1],[1,3]]),
         -Rational(286,343), -Rational(23,55296)),
    ]:
        a,b,c,d = M
        assert M.det()==p and gcd(*map(int,M))==1
        assert simplify((a*z+b)/(c*z+d)-z)==0
        alpha=simplify(p/(c*z+d)**2)
        assert simplify(alpha*alpha.conjugate())==1
        beta=simplify(alpha**e)
        tr=simplify(beta+1/beta)
        C=2-tr
        assert tr==expected_trace and C!=0
        P=diagonal(p).shift(K)
        S=slice_poly(p,K).shift(K)
        assert P.nth(0)==P.nth(1)==S.nth(0)==S.nth(1)==0
        assert P.nth(2)*S.nth(2)!=0
        assert P.nth(2)==C*S.nth(2)
        k=(P.nth(3)-2*C*S.nth(3))/(C*S.nth(2))
        assert k==expected_k
        print(f"p={p} K={K} e={e} trace={tr} C={C} kappa_disk={k} PASS")
    # Generic normalized cross, valid on a two-branch double-point
    # slice with nonzero first jet in the RAMIFIED parameter W=w^e.
    A,B,t,P2,P3,S2,S3,w=symbols("A B t P2 P3 S2 S3 w")
    C=2-t
    X=A+B*w
    N=A*A+t*A*B*w
    M=C*A*A+C*(2+t)*A*B*w
    p=P2+P3*A*w
    s=S2+S3*A*w
    f=expand((N*p-M*s)*X**2-N*M*X*w*S3)
    assert expand(f.coeff(w,0)-A**4*(P2-C*S2))==0
    assert expand(f.coeff(w,1).subs(P2,C*S2)
        -A**3*(A*A*(P3-2*C*S3)-2*C*B*S2))==0
    # Reuse generic rank-two multiplication, including split and
    # repeated-root sectors. Invertibility requires an independent norm proof.
    h,k,a,b,u=symbols("h k a b u")
    mat=Matrix([[a,-k*b],[b,a+h*b]])
    norm=a*a+h*a*b+k*b*b
    assert expand(mat.det()-norm)==0
    assert expand(rem((a+b*u)*(a+b*(h-u))-norm,u**2-h*u+k,u))==0
    print("generic cross jet and quadratic norm PASS")

if __name__=="__main__":
    main()
