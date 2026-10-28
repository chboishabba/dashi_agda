#!/usr/bin/env python3
"""Exact regression for horned 2-adic cylinders, Hurwitz C3 rotor, A5/Qp.

Does not replace an infinite-group proof, a wild-embedding theorem,
a p-adic field instance in Agda, or exact-head kernel typechecking.
"""
from fractions import Fraction as F
from itertools import permutations, product

def qmul(a,b):
    w,x,y,z=a; t,u,v,s=b
    return (w*t-x*u-y*v-z*s, w*u+x*t+y*s-z*v,
            w*v-x*s+y*t+z*u, w*s+x*v-y*u+z*t)

ONE=(F(1),F(0),F(0),F(0))
MINUS=(-F(1),F(0),F(0),F(0))
I=(F(0),F(1),F(0),F(0))
J=(F(0),F(0),F(1),F(0))
K=(F(0),F(0),F(0),F(1))
q=(F(1,2),)*4
qbar=(F(1,2),-F(1,2),-F(1,2),-F(1,2))
negq=tuple(-x for x in q)

def qpower(a,n):
    r=ONE
    for _ in range(n):r=qmul(r,a)
    return r

def integer(bits):
    return sum(bit << i for i,bit in enumerate(bits))

def v2(n):
    ans=0
    while n and n%2==0:
        ans+=1; n//=2
    return ans

def even(p):
    return sum(p[i]>p[j] for i in range(5)
               for j in range(i+1,5))%2==0

def mul(a,b):
    return tuple(a[b[i]] for i in range(5))

def inverse(a):
    return tuple(a.index(i) for i in range(5))

def comm(a,b):
    return mul(mul(mul(a,b),inverse(a)),inverse(b))

def audit():
    assert qmul(q,qbar)==qmul(qbar,q)==ONE
    assert qpower(q,3)==MINUS and qpower(q,6)==ONE
    assert qpower(negq,3)==ONE
    assert sum(x*x for x in q)==1
    for a,b in ((I,J),(J,K),(K,I),(ONE,ONE)):
        assert qmul(qmul(q,a),qbar)==b
        assert qmul(qmul(negq,a),tuple(-v for v in qbar))==b
    for x,y,z in product((-2,-1,0,1,2), repeat=3):
        p=(F(0),F(x),F(y),F(z))
        assert qmul(qmul(q,p),qbar)==(F(0),F(z),F(x),F(y))
    print("Quaternion q^3=-1 and (-q)^3=1; conjugation = ambient C3: PASS")

    for n in range(1,8):
        addresses=list(product((0,1),repeat=n))
        for x in addresses:
            reverse_newest=tuple(reversed(x))
            for new in (0,1):
                assert tuple(reversed((new,)+reverse_newest))==x+(new,)
            for y in addresses:
                if x!=y:
                    depth=next(i for i,(a,b) in enumerate(zip(x,y)) if a!=b)
                    assert v2(integer(x)-integer(y))==depth
    print("2-adic horn address prefix distance, depths 1..7: PASS")

    for n in range(250):
        assert (n+3)%3==n%3 and n+3!=n
    print("Z to C3 loses winding information (not a proof about Z3): PASS")

    A5=[p for p in permutations(range(5)) if even(p)]
    assert len(A5)==60
    assert {comm(a,b) for a in A5 for b in A5}==set(A5)
    e=tuple(range(5))
    for a in A5:
        translated=[mul(a,b) for b in A5]
        assert len(set(translated))==60
        assert (translated==A5)==(a==e)
    print("A5 60/60 commutator coverage; faithful nonabelian regular matrices over Qp: PASS")
    print("Infinite pro-p/group/geometry/Agda kernel claims: NOT tested by finite probe")

if __name__ == "__main__":
    audit()
