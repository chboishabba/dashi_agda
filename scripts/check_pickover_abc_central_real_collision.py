#!/usr/bin/env python3
"""Actual 99^k real-seed collision at 27-cube centre, certified by Machin.

Not a synthetic rational phase, not an unverified trigonometric estimate.
Donors: existing check_pickover_machin_factorial_phase.interval_pi,
consumer-indexed residual, jCoarse/jFine, signed-zero/27 cube.
"""
from fractions import Fraction
from check_pickover_machin_factorial_phase import interval_pi

def floor(q): return q.numerator // q.denominator

def trits(p,n):
    out=[0]*n
    for j in range(n-1,-1,-1):
        out[j],p=p%3,p//3
    assert p==0
    return tuple(out)

def main():
    exponents=(7,13,32,108,151,153)
    scale=10**(2*max(exponents)+65)
    lower,upper=interval_pi(scale)
    assert 0<lower<upper
    receipts={}
    for k in exponents:
        n=99**k
        left,right=Fraction(n*scale,2*upper),Fraction(n*scale,2*lower)
        winding=floor(left)
        assert floor(right)==winding
        a,b=left-winding,right-winding
        assert 0<a<=b<1
        answer=None
        for depth in range(1,12):
            lo,hi=floor(a*3**depth),floor(b*3**depth)
            assert lo==hi
            word=trits(lo,depth)
            first=next((v for v in word if v!=1),None)
            if first is not None:
                answer=(word,1 if first==0 else -1,depth)
                break
        assert answer is not None
        qlo=floor(Fraction(n*scale,upper))
        qhi=floor(Fraction(n*scale,lower))
        assert qlo==qhi
        assert answer[1]==(1 if qlo%2==0 else -1)
        receipts[k]=answer
        print("k",k,"prefix",''.join(map(str,answer[0])),
              "sign",answer[1],"first-noncentral",answer[2])
    assert receipts[7]==((1,1,0),1,3)
    assert receipts[13]==((1,1,2),-1,3)
    assert receipts[32]==((1,1,1,2),-1,4)
    assert receipts[108]==((1,1,1,0),1,4)
    assert receipts[151]==((1,1,1,1,1,1,2),-1,7)
    assert receipts[153]==((1,1,1,1,1,1,2),-1,7)
    assert receipts[108][0][:3]==receipts[151][0][:3]==(1,1,1)
    assert receipts[108][1]!=receipts[151][1]
    print("PASS exact Machin real seed: two opposite signs collide on the 27-centre 111")
    print("OPEN: cheap first-noncentral producer at 9999! power")
if __name__=="__main__":main()
