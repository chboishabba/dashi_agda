#!/usr/bin/env python3
"""Independent exact-rational CMP102 finite regression, not an Agda receipt."""
from fractions import Fraction as F
from math import factorial


def main():
    N = 128
    a = [F((-1)**n, factorial(2*n+2)) for n in range(N)]
    b = [F((-1)**n, factorial(2*n+3)) for n in range(N)]
    for n in range(N):
        m = 2*n+2
        def f(j):
            return F((-1)**(m-j), factorial(j)*factorial(m-j))
        even = sum(f(j) for j in range(0, m+1, 2))
        odd = sum(f(j) for j in range(1, m, 2))
        assert even+odd == 0
        assert sum(f(j) for j in range(m)) == -F(1, factorial(m))
        h = int(n == 0)-2*a[n]
        if n >= 1:
            h += sum(a[k]*a[n-1-k] for k in range(n))-2*b[n-1]
        if n >= 2:
            h += sum(b[k]*b[n-2-k] for k in range(n-1))
        assert h == (-1)**(n+1)*(even+odd) == 0
    print("PASS: 128 inclusive parity, 128 omitted endpoint negative controls, 128 shifted coefficients")


if __name__ == "__main__":
    main()
