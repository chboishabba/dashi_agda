#!/usr/bin/env python3
"""Original CMP102 bounded source parity row: exact natural/rational regression."""
from fractions import Fraction as F
from math import factorial

def signed(m,j):
    return F((-1)**(m-j), factorial(j)*factorial(m-j))

def a(k): return F(1, factorial(2*k+2))
def b(k): return F(1, factorial(2*k+3))

def run(N=128):
    checked={"even_interior":0,"odd_interior":0,"even_edge":0,"odd_edge":0,
             "even_row":0,"odd_row":0,"full_cancel":0,"exclusive_end_negative":0}
    for n in range(N):
        m=2*n+2
        # All k in original bounded sum k < suc n.
        for k in range(1,n+1):
            r=n-k
            assert m-2*k==2*r+2
            assert signed(m,2*k)==a(k-1)*a(r)
            checked["even_interior"]+=1
        for k in range(1,n):
            r=n-1-k
            assert m-(2*k+1)==2*r+3
            assert signed(m,2*k+1)==-b(k-1)*b(r)
            checked["odd_interior"]+=1
        assert signed(m,0)==a(n) and signed(m,m)==a(n)
        checked["even_edge"]+=1
        if n:
            assert signed(m,1)==-b(n-1)
            assert signed(m,m-1)==-b(n-1)
        else:
            assert signed(m,1)==-F(1)
        checked["odd_edge"]+=1
        even=sum((signed(m,2*k) for k in range(n+1)),F(0))+signed(m,m)
        odd=sum((signed(m,2*k+1) for k in range(n+1)),F(0))
        E=2*a(n)+sum((a(k)*a(n-1-k) for k in range(n)),F(0))
        O=F(1) if n==0 else 2*b(n-1)+sum((b(k)*b(n-2-k) for k in range(n-1)),F(0))
        assert even==E;checked["even_row"]+=1
        assert odd==-O;checked["odd_row"]+=1
        assert even+odd==0;checked["full_cancel"]+=1
        # Last even source endpoint is required; omitting it must fail.
        assert even-signed(m,m)+odd==-a(n)
        checked["exclusive_end_negative"]+=1
    print(checked, "TOTAL",sum(checked.values()))

if __name__=="__main__":run()
