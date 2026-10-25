#!/usr/bin/env python3
"""Exact finite Eisenstein/C3/CRT replay. Standard library only.
Companion to DASHI.Mathematics.NumberTheory.EisensteinNineCRTPhaseMaxCutExact.
NOT an Agda kernel receipt, RH proof, or real sine-sign determination.
"""
from dataclasses import dataclass
from math import factorial, gcd

@dataclass(frozen=True)
class R:
    x: int   # a modulo 81
    y: int   # a+b modulo 243 for a+b*omega
    def __post_init__(self):
        object.__setattr__(self, 'x', self.x % 81)
        object.__setattr__(self, 'y', self.y % 243)
    def __add__(self, b):
        return R(self.x + b.x, self.y + b.y)
    def __neg__(self):
        return R(-self.x, -self.y)
    def __sub__(self, b):
        return self + -b
    def __mul__(self, b):
        x,y,u,v=self.x,self.y,b.x,b.y
        return R(x*v+y*u-y*v, 3*x*v+3*y*u-2*y*v-3*x*u)
    def __pow__(self, e):
        out=ONE
        while e:
            if e & 1: out=out*self
            self=self*self
            e>>=1
        return out

def from_basis(a,b):
    return R(a,a+b)

ZERO=from_basis(0,0)
ONE=from_basis(1,0)
OMEGA=from_basis(0,1)
LAM=ONE-OMEGA

def all_elements():
    for x in range(81):
        for y in range(243):
            yield R(x,y)

def convolution(a,b):
    return (a[0]*b[0]+a[1]*b[2]+a[2]*b[1],
            a[0]*b[1]+a[1]*b[0]+a[2]*b[2],
            a[0]*b[2]+a[1]*b[1]+a[2]*b[0])

def power_poly(a,n):
    out=(ONE,ZERO,ZERO)
    while n:
        if n&1: out=convolution(out,a)
        a=convolution(a,a)
        n>>=1
    return out

def run():
    # lambda^9 is associated with 81(1-omega): HNF basis
    # (81,-81),(0,243), determinant 81*243=3^9.
    assert len(set(all_elements())) == 3**9 == 19683
    assert OMEGA**2 + OMEGA + ONE == ZERO
    assert OMEGA**3 == ONE
    assert LAM*LAM == -from_basis(0,3)
    assert from_basis(81,-81) == ZERO
    assert from_basis(0,243) == ZERO
    assert LAM**8 == R(0,81) and LAM**9 == ZERO

    elements=list(all_elements())
    filtration=[]
    cur=ONE
    for k in range(10):
        size=len({cur*r for r in elements})
        filtration.append(size)
        assert size==3**(9-k)
        cur=cur*LAM
    assert filtration==[19683,6561,2187,729,243,81,27,9,3,1]
    assert {r for r in elements if r*r==r}=={ZERO,ONE}
    assert sum(r.y%3 != 0 for r in elements)==2*3**8
    for r in elements:
        assert (r**(2*3**9)==ONE)==(r.y%3!=0)

    ninety_nine=from_basis(99,0)
    assert ninety_nine == R(18,99)
    assert ninety_nine**2 == R(0,81)
    assert ninety_nine**3 == ZERO

    T=(ONE,ONE,ONE)
    assert convolution(T,T)==(from_basis(3,0),)*3
    assert power_poly(T,5)!=(ZERO,)*3
    assert power_poly(T,6)==(ZERO,)*3
    # U=g-1, U^3=3g-3g^2, U^11=0.
    U=(-ONE,ONE,ZERO)
    assert power_poly(U,3)==(ZERO,from_basis(3,0),-from_basis(3,0))
    assert power_poly(U,11)==(ZERO,)*3

    assert 9999==9*11*101 and 1111==11*101
    assert gcd(99,101)==1 and pow(99,100,101)==1
    assert pow(10,2,101)==100 and 101==10**2+1
    E=factorial(9999)
    assert E%100==0
    e=pow(99,E,9999)
    assert e==4950 and (e%9,e%11,e%101)==(0,0,1)
    assert e*e%9999==e
    assert pow(99,E,1111)==506
    modulus=19683*11*101
    f=pow(99,E,modulus)
    assert f==2814669 and (f%19683,f%11,f%101)==(0,0,1)
    assert f*f%modulus==f
    assert pow(99,factorial(10000),modulus)==f

    print('PASS: R has 19683 elements, additive C81 x C243')
    print('PASS: ramified lambda filtration',filtration)
    print('PASS: local idempotents, lambda^9=0, 99^3=0, C3 transfer T^6=0')
    print('PASS: factorial CRT projectors 4950/9999, 506/1111, 2814669/'+str(modulus))
    print('LIMIT: finite algebra only; real-phase sign and RH remain unresolved')

if __name__ == '__main__':
    run()
