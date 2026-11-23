#!/usr/bin/env python3
"""Native YM CMP102 endpoint cut: independent exact Fraction source verification.

Finite arithmetic reference; no Agda kernel, no analytic/CMP physical promotion.
"""
from fractions import Fraction as Q
from math import factorial

def exp1(k): return Q(1, factorial(k))
def E(k): return exp1(2*k)
def O(k): return exp1(2*k+1)
def A(k): return exp1(2*k+2)
def B(k): return exp1(2*k+3)
def cauchy(u,v,n): return sum((u(k)*v(n-k) for k in range(n+1)), Q(0))
def epart(n):
    return 2*A(n) + (cauchy(A,A,n-1) if n else Q(0))
def opart(n):
    if n == 0: return Q(1)
    return 2*B(n-1)+(cauchy(B,B,n-2) if n>1 else Q(0))

def run(N=128):
    count={k:0 for k in ('shiftA','shiftB','even_endpoint','odd_singleton','odd_one','odd_endpoint','even_interior','odd_interior','signed_odd','row_even','row_odd','bracket','missing_endpoint')}
    for n in range(N):
        assert E(n+1)==A(n);count['shiftA']+=1
        assert O(n+1)==B(n);count['shiftB']+=1
        # All source natural Fin indices in each true row.
        for k in range(n):
            assert E(k+1)*E(n-k)==A(k)*A(n-1-k)
            count['even_interior']+=1
        for k in range(max(0,n-1)):
            assert O(k+1)*O(n-1-k)==B(k)*B(n-2-k)
            count['odd_interior']+=1
        ep=cauchy(E,E,n+1)
        op=cauchy(O,O,n)
        assert ep == epart(n);count['row_even']+=1
        assert op == opart(n);count['row_odd']+=1
        assert ep+(-op)==Q(0);count['bracket']+=1
        assert -op==cauchy(O,lambda k:-O(k),n)
        count['signed_odd']+=1
        assert ep-E(n+1)*E(0)-op == -A(n)
        count['missing_endpoint']+=1
        assert E(0)*E(n+1)==A(n) and E(n+1)*E(0)==A(n)
        count['even_endpoint']+=1
        if n == 0:
            assert op==O(0)*O(0)==Q(1)
            count['odd_singleton']+=1
        elif n == 1:
            assert op==2*B(0)
            count['odd_one']+=1
        else:
            assert O(0)*O(n)==B(n-1) and O(n)*O(0)==B(n-1)
            count['odd_endpoint']+=1
    print('PASS',count,'TOTAL',sum(count.values()),'degrees 0..',N-1)
if __name__ == '__main__': run()
