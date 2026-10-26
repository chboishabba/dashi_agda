#!/usr/bin/env python3
"""Exact base-10 round/factorial sine signs via integer Machin pi intervals.

Classical source: John Machin (1706) pi/4=4atan(1/5)-atan(1/239).
Each atan is an alternating rational series; error is explicitly bounded.
DASHI regression/consumer only. No transcendentally invalid CRT transfer.
"""
from math import factorial

def pi_bounds(k, guard=24):
    scale=10**(k+guard)
    def arctan_scaled(q):
        total=0; denominator=q; j=0; sign=1
        while True:
            t=scale//((2*j+1)*denominator)
            if not t: return total,j
            total+=sign*t
            sign=-sign;j+=1;denominator*=q*q
    a,na=arctan_scaled(5); b,nb=arctan_scaled(239)
    mid=16*a-4*b
    err=16*(na+2)+4*(nb+2)
    return mid-err,mid+err,scale

def exact_sign(k):
    lo,hi,scale=pi_bounds(k)
    assert 0<lo<hi
    n=10**k
    a=(n*scale)//hi;b=(n*scale)//lo
    assert a==b, f'certificate inconclusive at {k}'
    return (1 if a%2==0 else -1),a%2

def main():
    cases=sorted(set([1,2,3,4,5,6,10,20,30,40,50,100,999,1000]
                     +[factorial(n) for n in range(1,8)]))
    result={}
    for k in cases:
        s,parity=exact_sign(k)
        result[k]=s
        print(f'base=10 exponent={k} sine_sign={s:+d} floor_div_pi_parity={parity}')
    for n in range(1,7):
        a=factorial(n);b=factorial(n+1)
        print(f'factorial jump {n}!->{n+1}!: {result[a]:+d}->{result[b]:+d}')
    assert result[2]==-1 and result[3]==1
    assert 10**2%10==10**3%10
    assert result[120]==-1 and result[720]==1
    print('PASS exact base10 factorial and round signs; CRT non-descent')
if __name__=='__main__':main()
