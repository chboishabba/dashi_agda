#!/usr/bin/env python3
"""Exact local correspondence on the *original* j=0 curve y^2=x^3+1.

DASHI source donors: Lean #69 canonical cubic, split Jacobi, all-good-prime
Euler, and Agda conductor/CM receipts. No global Hecke/L-series theorem.

For odd p>3: chi_{-3}(p) = (+1 iff p == 1 mod 3).
For split p, with cubic psi and quadratic phi on F_p:
  J = sum_t psi(t)*phi(1-t) in Z[omega], omega^2+omega+1=0
  norm(J)=p, a_p=-(J+conjugate(J))=-(2*a-b).
For inert p: a_p=0; local elliptic polynomial 1+p*T^2.
Quadratic Dirichlet degree-one local factor is not the elliptic degree-two one.
"""
from sympy import primitive_root
SPLIT = (7,13,19,31,37,43,61,67,73,79)
INERT = (5,11,17,23,29,41,47)
OMEGA = ((1,0),(0,1),(-1,-1))

def phi(x,p):
    v=x%p
    if v==0:return 0
    return 1 if pow(v,(p-1)//2,p)==1 else -1

def psi_table(p):
    g=int(primitive_root(p))
    d={}
    t=1
    for i in range(p-1):
        d[t]=OMEGA[i%3]
        t=t*g%p
    return {0:(0,0),**d}

def ap(p):
    return -sum(phi(x**3+1,p) for x in range(p))

def main():
    cube_tests=0
    dedekind_checks=0
    for p in SPLIT+INERT:
        assert phi(-3,p)==(1 if p%3==1 else -1)
        trace=ap(p)
        # Exact inverse Euler polynomial for zeta_K = zeta_Q * L(chi_-3).
        # Split: (1-T)^2; inert: 1-T^2. Compare coefficients.
        chi=phi(-3,p)
        product=(1,-(1+chi),chi)
        expected=(1,-2,1) if chi==1 else (1,0,-1)
        assert product==expected
        dedekind_checks+=1
        if p%3==2:
            assert trace==0
            print(f"inert {p}: chi_-3=-1 a_p=0; Euler = 1+{p}*T^2")
            continue
        psi=psi_table(p)
        a=b=0
        for t in range(p):
            u,v=psi[t]
            k=phi(1-t,p)
            a+=k*u;b+=k*v
            actual=sum(pow(x,3,p)==t for x in range(p))
            expected=1+(2*u-v) if t else 1
            assert actual==expected
            cube_tests+=1
        assert a*a-a*b+b*b==p
        assert trace==-(2*a-b)
        print(f"split {p}: chi_-3=+1 J={a}+({b})*omega, norm={p}, a_p={trace}")
    assert cube_tests==430 and dedekind_checks==17
    print("PASS 430 cube fibres, 10 Jacobi norms/traces, 7 inert zero traces, 17 Dedekind local factorizations")
    print("OPEN primitive quadratic Dirichlet character to global Hecke and elliptic L-series")

if __name__=="__main__":main()
