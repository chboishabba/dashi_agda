#!/usr/bin/env python3
"""Exact original factorial complementary pair regression for YM CMP102.
A local reference only: not Agda typechecking or a YM physical receipt.
"""
from fractions import Fraction as F
from math import factorial

def main():
    results = dict(even_pair=0, odd_pair=0, even_boundary=0, odd_boundary=0)
    for n in range(128):
        m = 2*n+2
        a = lambda k: F(1, factorial(2*k+2))
        b = lambda k: F(1, factorial(2*k+3))
        for k in range(n):
            r = n-1-k
            j = 2*k+2
            assert m-j == 2*r+2
            assert F(1, factorial(j)*factorial(m-j)) == a(k)*a(r)
            results["even_pair"] += 1
        for k in range(max(n-1, 0)):
            r = n-2-k
            j = 2*k+3
            assert m-j == 2*r+3
            assert F(-1, factorial(j)*factorial(m-j)) == -b(k)*b(r)
            results["odd_pair"] += 1
        even = sum((F(1,factorial(j)*factorial(m-j)) for j in range(0,m+1,2)), F(0))
        odd = sum((F(1,factorial(j)*factorial(m-j)) for j in range(1,m,2)), F(0))
        assert even == 2*a(n)+sum((a(k)*a(n-1-k) for k in range(n)), F(0))
        results["even_boundary"] += 1
        assert odd == (F(1) if n == 0 else 2*b(n-1)+sum((b(k)*b(n-2-k) for k in range(n-1)), F(0)))
        results["odd_boundary"] += 1
    assert sum(results.values()) == 16385
    print("PASS: CMP102 exact original factorial pairs/boundaries", results, "total", sum(results.values()))

if __name__ == "__main__":
    main()
