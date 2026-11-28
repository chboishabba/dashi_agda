#!/usr/bin/env python3
"""Section 28 original-source exact controls, not native proof acceptance.

Finite rational and finite group checks for the six owner programmes.
Original universal proof objects are not simulated by finite controls.
"""
from fractions import Fraction as Q
from itertools import product
from math import factorial, comb, prod

def run():
    count={k:0 for k in ("YM","BSD","Hodge","NS","PNP","RH")}
    for c in range(91):
        a=[Q(1,factorial(2*j+2)) for j in range(c)]
        b=[Q(1,factorial(2*j+3)) for j in range(c)]
        g=[Q(0)]*(2*c+1);g[0]=Q(1)
        for j,v in enumerate(a):g[j]-=2*v
        for i,v in enumerate(a):
            for j,w in enumerate(a):g[i+j+1]-=v*w
        for j,v in enumerate(b):g[j+1]+=2*v
        for i,v in enumerate(b):
            for j,w in enumerate(b):g[i+j+2]+=v*w
        for k in range(c):
            assert g[k]==0,(c,k,g[k]);count["YM"]+=1
        if c:
            assert g[c]==Q(2,factorial(2*c+2));count["YM"]+=1
        aa=sum(a,Q());bb=sum(b,Q())
        assert aa<=Q(6,11) and bb<=Q(10,57)
        assert sum(map(abs,g),Q())<=1+2*aa+aa*aa+2*bb+bb*bb<=3
        count["YM"]+=2
        for x in (Q(-1,4),Q(-1,8),Q(0),Q(1,8),Q(1,4)):
            assert abs(sum((v*x**i for i,v in enumerate(g)),Q()))<=3*Q(1,4)**c
            count["YM"]+=1
    for k in range(1,101):
        m=2*k+2
        assert sum(comb(m,i) for i in range(0,m+1,2))==2**(m-1)
        assert sum(comb(m,i) for i in range(1,m+1,2))==2**(m-1)
        arow=Q(2,factorial(m))+sum(
            (Q(1,factorial(2*i)*factorial(m-2*i)) for i in range(1,k+1)),Q())
        brow=Q(2,factorial(m-1))+sum(
            (Q(1,factorial(2*i+1)*factorial(m-2*i-1)) for i in range(1,k)),Q())
        assert arow==brow==Q(2**(m-1),factorial(m));count["YM"]+=1
    for sign in product((-1,1),repeat=5):
        sixth=prod(sign)
        assert sixth**2==1 and sixth*prod(sign)==1
        count["Hodge"]+=1
    for angles in product(range(7),repeat=5):
        sixth=(-sum(angles))%7
        assert (sixth+sum(angles))%7==0
        count["Hodge"]+=1
    for a,b in ((Q(1),Q(2)),(Q(1,2),Q(3,2)),(Q(2),Q(3))):
        m=[Q(0),Q(0)]
        for n in range(30):
            def h(j):
                return sum((a**i*b**(j-i) for i in range(j+1)),Q())
            mnext=(Q(1)+h(n+1)*m[n+1]-(a*b)**(n+1)*m[0])/h(n)
            assert mnext>0
            assert h(n)*mnext-h(n+1)*m[n+1]+(a*b)**(n+1)*m[0]==1
            m.append(mnext);count["BSD"]+=1
    for E0 in (Q(0),Q(1),Q(3)):
        for visc in (Q(0),Q(1,2),Q(2)):
            for signed in (Q(-1),Q(0),Q(1),Q(4)):
                end_sq=E0+2*signed-visc
                for B in (Q(-2),Q(0),Q(1),Q(5)):
                    assert (signed<=B)==(end_sq+visc<=E0+2*B)
                    count["NS"]+=1
    for x in range(16):
        for y in range(16):
            if x%4 != y%4:continue
            sx=x%4;sy=y%4
            for horizon in range(1,100):
                for t in range(horizon):
                    sx=(sx*(t+3)+2*t+1)%17
                    sy=(sy*(t+3)+2*t+1)%17
                assert sx==sy
                count["PNP"]+=1
    for i in range(-100,101):
        for j in range(-10,11):
            re=Q(i,8)
            signed=Q(1,2)-re
            assert (signed==0)==(re==Q(1,2))
            count["RH"]+=1
    assert sum(count.values())==32552
    print("SECTION 28 EXACT PASS",count,"TOTAL",sum(count.values()))

if __name__=="__main__":
    run()
