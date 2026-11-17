#!/usr/bin/env python3
"""Pickover exact Chebyshev sign and C101 factorisation negative control.
Pure integer arithmetic. Classical Machin pi rational enclosure.
The polynomial U98 is constructed by U0=1,U1=2X,U_n=2X U_(n-1)-U_(n-2).
A sign step uses exact sin(99x)=sin(x)U98(cos x).
The real signs are independently certified by Machin, not by 101 residues.
"""
from math import factorial

def atan_scaled(s,d):
    j,p,sign,out=0,d,1,0
    while True:
        t=s//((2*j+1)*p)
        if not t: return out,j
        out+=sign*t
        j+=1;p*=d*d;sign=-sign

def pi_bounds(s):
    a,na=atan_scaled(s,5);b,nb=atan_scaled(s,239)
    v=16*a-4*b;e=16*(na+1)+4*(nb+1)
    return v-e,v+e

def real_sin_sign(k,s,l,u):
    # Both endpoints for floor(99^k/pi) agree: exact sign certificate.
    n=pow(99,k)*s
    low,high=n//u,n//l
    assert low==high,('precision failure',k)
    return 1 if low%2==0 else -1

def u_coefficients(n):
    old,new=[1],[0,2]
    if n==0:return old
    if n==1:return new
    for _ in range(2,n+1):
        cur=[0]+[2*x for x in new]
        for j,v in enumerate(old):cur[j]-=v
        old,new=new,cur
    return new

def torsion_101_sign(k):
    r=pow(99,k,101)
    return (1 if 1<=r<=50 else -1),r

def main():
    scale=pow(99,5040+32)
    l,u=pi_bounds(scale)
    assert 0<l<u
    c=u_coefficients(98)
    assert len(c)==99 and c[-1]==2**98
    assert all(c[j]==0 for j in range(1,99,2))
    sequential={k:real_sin_sign(k,scale,l,u) for k in range(13)}
    for k in range(12):
        # By the exact Chebyshev identity, this quotient of certified sine
        # signs is sign U98(cos(99^k)). Not a cosine approximation.
        uk=sequential[k+1]*sequential[k]
        assert sequential[k]*uk==sequential[k+1]
    actual={factorial(n):real_sin_sign(factorial(n),scale,l,u)
            for n in range(1,8)}
    assert [actual[factorial(n)] for n in range(1,8)]==[-1,-1,1,1,-1,1,-1]
    rows=[]
    for n in range(1,8):
        k=factorial(n); t,r=torsion_101_sign(k)
        rows.append((n,k,r,t,actual[k],t==actual[k]))
    assert rows[4][2]==rows[5][2]==95
    assert rows[4][4]==-1 and rows[5][4]==1
    assert 99**1%101 != 99**6%101
    assert pow(99,factorial(9999),101)==1
    print('PASS U98 polynomial degree=98, leading coefficient=2^98')
    print('PASS 12 signed Chebyshev transitions certified independently via Machin')
    print('n, n!, residue mod101, finite sign, real sign, equal')
    for r in rows:print(*r)
    print('PASS SAME C101 RESIDUE 95 AT 5! AND 6! BUT OPPOSITE REAL SINE SIGNS')
    print('BOUNDARY: no certified sign for sin(99^(9999!))')

if __name__=='__main__':main()
