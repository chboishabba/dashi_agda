#!/usr/bin/env python3
"""369 signed-circle observer vs exact repo Q9 phase quotient: no conflation.
DASHI / original finite model: TernaryEndomorphismPhaseQuotientExact,
PhaseQuotientNonaryGroupSeparationExact. Finite rational circle control.
"""
from fractions import Fraction

def circle_sign(x):
    x=x%1
    if x==0 or x==Fraction(1,2): return 0
    return 1 if x<Fraction(1,2) else -1

def sector(x,q): return ((x%1)*q).__floor__()
def power(x,m):return m*x%1
def ternary_pair(n):return divmod(n,3)

def main():
    # 3, 9 and 27 circle addresses make nested partitions.
    for n in range(27):
        assert sector(Fraction(2*n+1,54),3)==n//9
        assert sector(Fraction(2*n+1,54),9)==n//3
        assert sector(Fraction(2*n+1,54),27)==n
        assert ternary_pair(n//3)==divmod(n//3,3)
    # The middle ninth intersects both signed semicircles.
    a,b=Fraction(17,36),Fraction(19,36)
    assert sector(a,9)==sector(b,9)==4
    assert circle_sign(a)==1 and circle_sign(b)==-1
    # Under the target factor power action their signs again differ
    # in the opposite direction despite having the same nine-address.
    assert circle_sign(power(a,99))==-1
    assert circle_sign(power(b,99))==1
    # Coarse circle sector after powering is NOT a function of
    # the original sector: within the same ninth find unequal outputs.
    x,y=Fraction(1,108),Fraction(2,108)
    assert sector(x,9)==sector(y,9)==0
    assert sector(power(x,99),9)!=sector(power(y,99),9)
    # Actual repository Q9=(F3)^2: every additive element has order <=3.
    # Cyclic nine-sector labels Z/9 contain elements of order 9.
    for a0 in range(3):
        for a1 in range(3):
            assert (3*a0%3,3*a1%3)==(0,0)
    assert (3*1)%9 != 0
    print('PASS: nested circle 3/9/27 sectors and signed fibre collision')
    print('PASS: 99-power action cannot descend through sector-nine alone')
    print('PASS: Q9=(C3)^2 is not cyclic circle C9 as a group')
    print('OPEN: retained-residual analytic power cocycle and terminal sign')
if __name__=='__main__':main()
