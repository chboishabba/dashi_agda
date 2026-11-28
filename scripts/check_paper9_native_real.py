#!/usr/bin/env python3
"""Exact finite reference for the native Bishop midpoint/order constructor."""
from fractions import Fraction as F
from math import isqrt

A, B, C = 13591409, 545140134, 640320**3

def main():
    p, q, t = 1, 1, 0
    prefixes = [F(0)]
    for n in range(10):
        a,b = (1,1) if n == 0 else (-24*(2*n-1)*(6*n-5)*(6*n-1),C*n**3)
        p *= a; q *= b; t = t*b+p*(A+B*n)
        prefixes.append(F(t,q))
    W = []
    for k in range(257):
        j=1+(k+4)//41; scale=2**(k+2); r=isqrt(10005*scale**2)
        lo,hi=sorted(prefixes[j:j+2])
        L,U=F(426880*r,scale)/hi,F(426880*(r+1),scale)/lo
        assert 0<=U-L<=F(1,2**k)
        W.append((L,U,(L+U)/2))
    for m in range(1,129):
        for n in range(1,129):
            l,u,_=W[min(m,n)]
            x,y=W[m][2],W[n][2]
            assert l<=x<=u and l<=y<=u
            assert abs(x-y)<=u-l<=F(1,m)+F(1,n)
    for k in range(129):
        L,U,_=W[k]
        for n in range(1,129):
            l,u,x=W[2*n]
            assert L-x<=u-l<=F(1,n)
            assert x-U<=u-l<=F(1,n)
            assert x-L>=-F(1,n) and U-x>=-F(1,n)
    print('257 width controls; 16384 native regularity pairs; 16512 paired native order controls PASS')

if __name__=='__main__':main()
