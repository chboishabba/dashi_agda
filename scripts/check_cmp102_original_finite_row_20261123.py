#!/usr/bin/env python3
"""Exact original signed parity row, boundary and native A/B aggregation."""
from fractions import Fraction as F
from math import factorial

def a(k): return F(1, factorial(2*k+2))
def b(k): return F(1, factorial(2*k+3))
def f(m,j): return F((-1)**(m-j), factorial(j)*factorial(m-j))

def run(N=128):
    counts={"even_original_row":0,"odd_original_row":0,"even_interior":0,"odd_interior":0,"signed_full_row":0}
    for n in range(N):
        m=2*n+2
        even=sum((f(m,2*k) for k in range(n+1)),F(0))+f(m,m)
        odd=sum((f(m,2*k+1) for k in range(n+1)),F(0))
        E=2*a(n)+sum((a(k)*a(n-1-k) for k in range(n)),F(0))
        O=F(1) if n==0 else 2*b(n-1)+sum((b(k)*b(n-2-k) for k in range(n-1)),F(0))
        assert even==E;counts["even_original_row"]+=1
        assert odd==-O;counts["odd_original_row"]+=1
        assert even+odd==0;counts["signed_full_row"]+=1
        for k in range(n):
            assert f(m,2*k+2)==a(k)*a(n-1-k)
            counts["even_interior"]+=1
        for k in range(max(0,n-1)):
            assert f(m,2*k+3)==-b(k)*b(n-2-k)
            counts["odd_interior"]+=1
    print(counts,"total",sum(counts.values()))

if __name__=="__main__":run()
