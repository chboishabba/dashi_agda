"""Exact projective cross cancellation, with certified decimal floor."""
from math import gcd,isqrt
from fractions import Fraction as F
from time import perf_counter
from statistics import median
import hashlib,sys
A,B,C=13591409,545140134,640320**3

def split(a,b,mode):
    if a==b:return 1,1,0
    if b-a==1:
        p,q=(1,1) if a==0 else (-24*(2*a-1)*(6*a-5)*(6*a-1),C*a**3)
        t=(A+B*a)*p
    else:
        m=(a+b)//2
        p,q,t=split(a,m,mode);P,Q,T=split(m,b,mode)
        if mode>=2:
            g=gcd(p,Q);p//=g;Q//=g
        p,q,t=p*P,q*Q,t*Q+p*T
    if mode in (1,2):
        g=gcd(gcd(p,q),t);p//=g;q//=g;t//=g
    return p,q,t

def interval(n,bits,mode):
    p,q,t=split(0,n,mode);v=F(t,q)
    nxt=F(p,q)*F(-24*(2*n-1)*(6*n-5)*(6*n-1),C*n**3)*(A+B*n)
    lo,hi=sorted((v,v+nxt));assert lo>0
    s=1<<bits;z=isqrt(10005*s*s)
    return F(426880*z,s)/hi,F(426880*(z+1),s)/lo

def certified(d,mode):
    n=d//14+2;bits=4*d+32;scale=10**d
    while True:
        l,u=interval(n,bits,mode)
        x=l.numerator*scale//l.denominator;y=u.numerator*scale//u.denominator
        if x==y:
            return str(x),n,bits
        n+=max(1,n//16);bits+=max(32,bits//16)

def main():
    from sympy import Matrix,symbols,expand
    p,q,t,P,Q,T,g=symbols('p q t P Q T g')
    assert (Matrix([[g*p,t],[0,q]])*Matrix([[P,T],[0,g*Q]])-g*Matrix([[p*P,t*Q+p*T],[0,q*Q]])).applyfunc(expand)==Matrix.zeros(2)
    count=0
    for a in range(20):
        for b in range(a,a+20):
            p,q,t=split(a,b,0)
            for mode in (1,2,3):
                P,Q,T=split(a,b,mode)
                assert p*Q==P*q and t*Q==T*q
                if mode!=3:assert gcd(gcd(P,Q),T)==1
                count+=1
    print('PASS',count,'exact subinterval comparisons',flush=True)
    if hasattr(sys,'set_int_max_str_digits'):sys.set_int_max_str_digits(0)
    for d in (1000,10000,50000):
        ref=None;rows=[]
        for mode in (0,1,2,3):
            samples=[]
            for _ in range(3):
                st=perf_counter();s,n,bits=certified(d,mode);samples.append(perf_counter()-st)
            if ref is None:ref=s
            else:assert s==ref
            p,q,t=split(0,n,mode)
            rows.append((mode,round(median(samples)*1000,3),sum(abs(x).bit_length() for x in (p,q,t)),n,bits))
        print(d,rows,hashlib.sha256(ref.encode()).hexdigest(),flush=True)
if __name__=='__main__':main()
