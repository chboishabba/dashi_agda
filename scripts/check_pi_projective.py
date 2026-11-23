"""Projective Chudnovsky split; classical identity and alternating tail retained."""
from fractions import Fraction as F
from math import gcd,isqrt,factorial
from statistics import median
from time import perf_counter
A,B,C=13591409,545140134,640320**3

def split(a,b,mode):
    if a==b:return 1,1,0
    if b-a==1:
        p,q=(1,1) if a==0 else (-24*(2*a-1)*(6*a-5)*(6*a-1),C*a**3)
        t=(A+B*a)*p
    else:
        m=(a+b)//2
        p,q,t=split(a,m,mode); P,Q,T=split(m,b,mode)
        p,q,t=p*P,q*Q,t*Q+p*T
    if mode:
        g=gcd(gcd(p,q),t);p//=g;q//=g;t//=g
    return p,q,t

def interval(n,bits,mode):
    p,q,t=split(0,n,mode);v=F(t,q)
    nxt=F(p,q)*F(-24*(2*n-1)*(6*n-5)*(6*n-1),C*n**3)*(A+B*n)
    lo,hi=sorted((v,v+nxt));assert lo>0
    s=1<<bits;z=isqrt(10005*s*s)
    return F(426880*z,s)/hi,F(426880*(z+1),s)/lo

def main():
    from sympy import Matrix,symbols,expand
    p,q,t,P,Q,T,g,h=symbols('p q t P Q T g h')
    X=Matrix([[p,t],[0,q]]);Y=Matrix([[P,T],[0,Q]])
    assert ((g*X)*(h*Y)-g*h*X*Y).applyfunc(expand)==Matrix.zeros(2)
    count=0
    for a in range(20):
        for b in range(a,a+20):
            p,q,t=split(a,b,0);P,Q,T=split(a,b,1)
            assert p*Q==P*q and t*Q==T*q and gcd(gcd(P,Q),T)==1
            count+=1
    for n in range(1,15):
        p,q,t=split(0,n,1)
        assert F(t,q)==sum((F((-1)**k*factorial(6*k)*(A+B*k),factorial(3*k)*factorial(k)**3*C**k) for k in range(n)),F(0))
    print('PASS projective',count,'factorial 14',flush=True)
    for digits in (1000,10000,50000):
        n=digits//14+2;bits=4*digits+32; rows=[];ref=None
        for mode in (0,1):
            samples=[]
            for _ in range(3):
                start=perf_counter();l,u=interval(n,bits,mode);samples.append(perf_counter()-start)
            if ref is None:ref=l,u
            else:assert ref==(l,u)
            assert u-l<=F(1,10**digits)
            p,q,t=split(0,n,mode)
            rows.append((round(median(samples)*1000,3),sum(abs(x).bit_length() for x in (p,q,t))))
        print(digits,n,rows,flush=True)
if __name__=='__main__':main()
