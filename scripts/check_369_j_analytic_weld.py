#!/usr/bin/env python3
"""Exact arithmetic regressions for the original 369 lattice/q/Legendre seam.
Classical analytic identities are justified in the accompanying roadmap, not
proved by finite tests. No claim of an Agda kernel receipt.
"""
from fractions import Fraction as F
from time import perf_counter
from sympy import symbols, expand, factor, pi, I, factorial, zeta, divisors

def main():
    start=perf_counter()
    a,b,m,n,x,y,r=symbols('a b m n x y r', real=True)
    Q=a*a-a*b+b*b; V=a*b*(b-a); W=(a+b)*(2*a-b)*(a-2*b)
    assert expand(4*Q**3-27*V**2-W**2)==0
    assert expand((1+x*x+y*y)*((m*x+n)**2+(m*y)**2)-y*y*(m*m+n*n)-((x*n+m*(x*x+y*y))**2+(m*x+n)**2))==0
    # Positive telescoping bound per shell: r>=1, compare with integral gap.
    # For r>=2, 1/(r-1)^p-1/r^p >= p/r^(p+1).
    t=symbols('t', nonnegative=True)
    for p in (2,4):
        poly=expand((r**p-(r-1)**p)*r-p*(r-1)**p).subs(r,t+2).expand()
        assert all(c>=0 for c in poly.as_poly(t).all_coeffs())
    for k,expected in ((4,240),(6,-504)):
        assert (2*(-2*pi*I)**k/factorial(k-1)/(2*zeta(k))).simplify()==expected
    assert 2**6*3**3==1728 and 10*3**9+54==196884
    # Actual q coefficients via independent divisor enumeration and Lambert sum.
    N=64
    for power in (3,5):
        coeff=[0]*(N+1)
        for d in range(1,N+1):
            for j in range(d,N+1,d): coeff[j]+=d**power
        assert all(coeff[j]==sum(int(d)**power for d in divisors(j)) for j in range(1,N+1))
    points=0; shells=0
    for X,Y in [(F(0),F(1)),(F(1,2),F(1,3)),(F(-2,3),F(5,4)),(F(2),F(3))]:
        C=(1+X*X+Y*Y)/(Y*Y)
        for R in range(1,17):
            coords=[(M,N) for M in range(-R,R+1) for N in range(-R,R+1) if max(abs(M),abs(N))==R]
            assert len(coords)==8*R
            sums={4:F(0),6:F(0)}
            for M,N in coords:
                den=(M*X+N)**2+(M*Y)**2
                assert den>0 and F(1,den)<=C/R**2
                for k in sums: sums[k]+=F(1,den)**(k//2)
                points+=1
            for k,v in sums.items(): assert v<=8*C**(k//2)/R**(k-1)
            shells+=1
    # Local nonvanishing: E4(i)>1, E6(omega)>1 using q=-r,
    # 0<r<1/128 via pi sqrt(3)>5 and exp(5)>128.
    assert sum(F(5**k,int(factorial(k))) for k in range(12))>128
    assert F(223,71)**2*3>25
    # tail sum from n=2: sigma5(n)<=n^6; ratio <=(3/2)^6*r <1/2.
    assert F(3,2)**6/F(128)<F(1,2)
    assert 2*2**6/F(128)<=1  # tail <= r (strict for r<1/128)
    print(f'PASS: {points} reciprocal points, {shells} shells, 128 Lambert coefficients; symbolic identities and local nonvanishing bounds; {perf_counter()-start:.4f}s')

if __name__=='__main__': main()
