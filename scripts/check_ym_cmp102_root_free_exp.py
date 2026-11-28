#!/usr/bin/env python3
"""Exact finite regression of CMP102 root-free exponential algebra."""
from math import factorial
import sympy as S

def main():
    for n in range(1, 41):
        c = sum(S.Rational((-1)**n, factorial(2*k)*factorial(2*(n-k)))
                for k in range(n+1))
        d = sum(S.Rational((-1)**(n-1), factorial(2*k+1)*factorial(2*(n-1-k)+1))
                for k in range(n))
        assert c+d == 0
    a,b,c,d,e,f,g,h = S.symbols("a b c d e f g h", real=True)
    def mul(q,r):
        a,b,c,d=q
        e,f,g,h=r
        return S.Matrix([a*e-b*f-c*g-d*h,a*f+b*e+c*h-d*g,
                         a*g-b*h+c*e+d*f,a*h+b*g-c*f+d*e])
    q=S.Matrix([a,b,c,d])
    r=S.Matrix([e,f,g,h])
    p=mul(q,r)
    assert S.expand(p.dot(p)-q.dot(q)*r.dot(r)) == 0
    delta=p-r
    z=q-S.Matrix([1,0,0,0])
    assert S.expand(delta.dot(delta)-z.dot(z)*r.dot(r)) == 0
    print("40 exact coefficients; Hamilton norm and right displacement: PASS")

if __name__ == "__main__":
    main()
