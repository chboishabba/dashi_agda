#!/usr/bin/env python3
"""Exact finite replay of Jacobi shell BIDI and signed theta polynomials.
Independent diagnostic; not a Lean/Agda acceptance certificate.
"""
from itertools import product
from math import isqrt
from sympy import symbols, expand, divisor_sigma


def H(x):
    a,b,c,d=x
    return a+b+c+d,a+b-c-d,a-b+c-d,a-b-c+d


def flip(x):
    return (-x[0],*x[1:])


def norm(x):
    return sum(a*a for a in x)


def convolution(a,b,N):
    return [sum(a[k]*b[n-k] for k in range(n+1)) for n in range(N+1)]


def main():
    a,b=symbols('a b'); Q=a*a-a*b+b*b; V=a*b*(b-a); W=(a+b)*(2*a-b)*(a-2*b)
    assert expand(4*Q**3-W**2-27*V**2)==0
    assert expand(Q.subs({a:-a,b:b-a},simultaneous=True)-Q)==0
    assert expand(W.subs({a:-a,b:b-a},simultaneous=True)-W)==0
    assert expand(V.subs({a:-a,b:b-a},simultaneous=True)+V)==0
    counts={'polynomial':4,'integer_bidi':0,'half_bidi':0,'shells':0,'jacobi':0,'eisenstein':0,'delta':0}
    N=64
    odd=[set() for _ in range(N+1)]
    evenhalf=[set() for _ in range(N+1)]
    oddhalf=[set() for _ in range(N+1)]
    for x in product(range(-isqrt(N),isqrt(N)+1),repeat=4):
        n=norm(x)
        if n>N or sum(x)%2==0: continue
        y=H(x); assert all(a%2 for a in y) and sum(y)%4==0
        assert norm(y)==4*n and tuple(a//4 for a in H(y))==x
        odd[n].add(x);counts['integer_bidi']+=1
    for y in product(range(-isqrt(4*N),isqrt(4*N)+1),repeat=4):
        if not all(a%2 for a in y):continue
        m=norm(y)
        if m>4*N or m%4:continue
        n=m//4
        if sum(y)%4==0:
            evenhalf[n].add(y); z=y
        else:
            oddhalf[n].add(y); z=flip(y)
        assert all(a%4==0 for a in H(z))
        x=tuple(a//4 for a in H(z)); assert x in odd[n] and H(x)==z and flip(flip(y))==y
        counts['half_bidi']+=1
    for n in range(N+1):
        assert {H(x) for x in odd[n]}==evenhalf[n]
        assert {flip(y) for y in evenhalf[n]}==oddhalf[n]
        counts['shells']+=2
    def mul(a,b):return convolution(a,b,N)
    def add(a,b):return [x+y for x,y in zip(a,b)]
    def sub(a,b):return [x-y for x,y in zip(a,b)]
    def fourth(a):return mul(mul(a,a),mul(a,a))
    s=[int(n==0)+2*sum(j*j==n for j in range(1,n+1)) for n in range(N+1)]
    h=[sum(j*(j+1)==n for j in range(n+1)) for n in range(N+1)]
    A=[0]+[16*x for x in fourth(h)[:-1]];B=fourth(s);C=fourth([(-1)**n*x for n,x in enumerate(s)])
    E4=add(sub(mul(A,A),mul(A,B)),mul(B,B)); W=mul(mul(add(A,B),sub(add(A,A),B)),sub(A,add(B,B)))
    V=mul(mul(A,B),sub(B,A));V2=mul(V,V)
    D=sub([4*x for x in mul(mul(E4,E4),E4)],mul(W,W))
    for n in range(N+1):
        assert B[n]==A[n]+C[n] and A[n]==len(evenhalf[n])+len(oddhalf[n]);counts['jacobi']+=2
        e4=1 if n==0 else 240*int(divisor_sigma(n//2,3)) if n%2==0 else 0
        e6=1 if n==0 else -504*int(divisor_sigma(n//2,5)) if n%2==0 else 0
        assert E4[n]==e4 and W[n]==2*e6;counts['eisenstein']+=2
        assert D[n]==27*V2[n];counts['delta']+=1
    print(counts, sum(counts.values()), 'PASS')
    print('E4, E6 first q coefficients:',E4[2],W[2]//2)
if __name__=='__main__':main()
