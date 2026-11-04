#!/usr/bin/env python3
"""Independent exact-Fraction rational complex ABL rate fixtures.

Proof obligations: each certified controlled pulse satisfies c*c+s*s=1,
2*c*c<=1; norm-square of complex disturbance product <=1.
The two negative controls deliberately violate these inputs.
NOT Agda, a physical correlated many-body system, or an OS mass gap.
"""
from fractions import Fraction as Q
from random import Random

def cmul(a,b):
    return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def born(a):
    return a[0]*a[0]+a[1]*a[1]
def prod(xs):
    result=(Q(1),Q(0))
    for x in xs:result=cmul(result,x)
    return result

pulses=[(Q(3,5),Q(4,5)),(Q(5,13),Q(12,13)),
        (Q(8,17),Q(15,17)),(Q(7,25),Q(24,25)),
        (Q(20,29),Q(21,29))]
gammas=[(Q(1),Q(0)),(Q(0),Q(1)),(Q(3,5),Q(4,5)),
        (Q(1,2),Q(0)),(Q(0),Q(0)),(Q(5,13),Q(12,13))]

def main():
    assert all(c*c+s*s==1 and 2*c*c<=1 for c,s in pulses)
    for seed in range(3000):
        rng=Random(seed)
        k=rng.randrange(0,17)
        selected=[rng.choice(pulses) for _ in range(k)]
        selected_gamma=[rng.choice(gammas) for _ in range(rng.randrange(0,9))]
        gamma=prod(selected_gamma)
        overlap=prod([(c,Q(0)) for c,_ in selected])
        wrong=born(cmul(gamma,overlap))
        product=Q(1)
        for c,_ in selected: product*=c*c
        assert wrong==born(gamma)*product
        assert born(gamma)<=1
        assert 2**k*product<=1
        assert 2**k*wrong<=1
        assert (2**k+1)*wrong<=1+wrong
        assert wrong/(1+wrong)<=Q(1,2**k+1)
        assert 1+wrong>0
    assert Q(1,2)>Q(1,3) # invalid pulse c=1,k=1
    assert Q(4,5)>Q(1,2) # invalid gamma norm-square 4, k=0
    print("PASS: 21000 exact complex/ABL identities and inequalities, 3000 fixtures")
    print("PASS: both invalid-assumption negative controls")
    print("REFERENCE ONLY: Agda kernel and physical P01/P07 still OPEN")

if __name__=="__main__":
    main()
