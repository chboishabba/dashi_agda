#!/usr/bin/env python3
"""BR35: exact sufficient damped cone bounds for actual BR34 D/E.
No uniform glancing or variable-coefficient estimate is asserted.
All bounds use component max norms and BR15 Dirichlet Green estimates.
"""
from fractions import Fraction as F

k=F(3,5)

def eps(gamma,c1,c0):
    a=2*F(c1)/gamma+F(c0)/gamma**2
    rho=6*a
    assert rho<1
    return 18*a/(1-rho)

def metric_D(K):
    H=F(2,3)
    p=F(4,3)+4*K
    b=F(4,3)*(1+K*p)
    a=4*H+F(4,3)*(4*K*b+F(4,3)*p+2)
    return max(H,b/2,(a+p)/2)

def metric_E(K):
    H=F(2,3);p=F(4)
    bs=F(4,3)*(1+K*p)
    b=max(bs,K*(3*K*bs+1))
    a=4*H+F(8,3)
    return max(H,b/2,(a+p)/2)

def gauge_D(K):return max(F(2),1+2*K)
def gauge_E(K):return 1+K/2

def factors(K,gamma):
    K=F(K);gamma=F(gamma)
    assert K>=1 and gamma>=16*2*k
    em=eps(gamma,1536,F(30832,25))
    eg=eps(gamma,8,F(1239,100))
    dm=8*em+60*k/gamma
    dg=2*eg+5*k/gamma
    return metric_D(K)*dm,metric_E(K)*dm,gauge_D(K)*dg,gauge_E(K)*dg

def run():
    for K in (1,2,4,8,16,32):
        gamma=10**7
        while max(factors(K,gamma))>=F(1,2):gamma*=10
        vals=factors(K,gamma)
        assert max(vals)<F(1,2)
        print(f'K={K:2d} gamma={gamma:12d} metric-D={float(vals[0]):.6g} metric-E={float(vals[1]):.6g} gauge-D={float(vals[2]):.6g} gauge-E={float(vals[3]):.6g}')
    # No single fixed threshold from these constants as K tends to infinity.
    assert metric_D(F(32))>metric_D(F(16)) and metric_E(F(32))>metric_E(F(16))
    print('PASS exact rational sufficient cone contractions (24); Neumann norm <=2, not full glancing or undamped stability')

if __name__=='__main__':run()
