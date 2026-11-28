#!/usr/bin/env python3
"""Exact symbolic reciprocal disk and period weld, independent of kernel.
The CM root/analytic series identity is not proved by this checker.
"""
import sympy as s

def main():
    a,b,d,w,A,B,t,P2,P3,S2,S3=s.symbols("a b d w A B t P2 P3 S2 S3", nonzero=True)
    z=s.symbols("z")
    checks=0
    def check(expr):
        nonlocal checks
        assert s.cancel(expr)==0, expr
        checks+=1
    def cm(expr):
        nonlocal checks
        n,den=s.fraction(s.cancel(expr))
        assert s.rem(n,z*z+z+41,z)==0,expr
        assert s.rem(den,z*z+z+41,z)!=0,expr
        checks+=1
    alpha=-z/(z+1)
    undisk=lambda v:z+(2*z+1)*v/(1-v)
    cm(alpha+1/alpha+s.Rational(81,41))
    cm(-41/(undisk(w)+1)-undisk(alpha*w))
    cm(-41/undisk(w)-1-undisk(w/alpha))
    cm((undisk(w)-z)/(undisk(w)+z+1)-w)
    u=d*w/(1-w)
    germ=s.series(a*u+b*u*u/2,w,0,3).removeO()
    check(germ-a*d*w-(a*d+b*d*d/2)*w*w)
    check(2*(a*d+b*d*d/2)/(a*d)**2-b/a**2-2/(d*a))
    beta=s.symbols("beta",nonzero=True)
    X=A+B*w
    Xp=beta*(A+B*beta*w)
    Xm=(A+B*w/beta)/beta
    N=Xp*Xm
    M=(X-Xp)*(X-Xm)
    tr=beta+1/beta
    check(N.subs(w,0)-A*A)
    check(M.subs(w,0)-(2-tr)*A*A)
    check(s.diff(N,w).subs(w,0)-tr*A*B)
    check(s.diff(M,w).subs(w,0)-(2-tr)*(1+tr)*A*B)
    cm(s.diff(N,w).subs(w,0).subs(beta,alpha)+s.Rational(81,41)*A*B)
    cm(s.diff(M,w).subs(w,0).subs(beta,alpha)-s.Rational(163,1681)*A*B)
    p=P2+P3*w*X
    q=S2+S3*w*X
    cross=(N*p-M*q)*X**2-N*M*X*w*S3
    check(cross.subs(w,0)-A**4*(P2-(2-tr)*S2))
    der=s.diff(cross,w).subs(w,0).subs(P2,(2-tr)*S2)
    check(der-A**3*(A**2*(P3-2*(2-tr)*S3)-2*(2-tr)*B*S2))
    K=-640320**3
    kappa=-s.Rational(77859659565707,19943834790540897829879824384000)
    # Euler correction: kappa = (-E*x*y+3*x^3+4*y^2)/(6*K*y^2)
    # + x/(2*K*p*y). Eliminate x^3/y^2 via j*z=1728.
    corr=3*s.Rational(K,K-1728)+4-6*K*kappa
    check(corr-s.Rational(77265280,90856689))
    check((1-corr)/6-s.Rational(13591409,545140134))
    check(s.Rational(545140134,426880)**2-10005*163*(1-s.Rational(1728,K)))
    print("PASS",checks,"exact symbolic CM disk/period weld identities")

if __name__=="__main__":
    main()
