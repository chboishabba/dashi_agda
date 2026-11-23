#!/usr/bin/env python3
from fractions import Fraction as F
from math import factorial

def main():
    N = 128
    a = [F(1, factorial(2*n+2)) for n in range(N)]
    b = [F(1, factorial(2*n+3)) for n in range(N)]
    counts = [0]*4
    for n in range(N):
        m = 2*n+2
        even = sum(F(1,factorial(j)*factorial(m-j)) for j in range(0,m+1,2))
        odd = sum(F(1,factorial(j)*factorial(m-j)) for j in range(1,m,2))
        ae = 2*a[n]+sum(a[k]*a[n-1-k] for k in range(n))
        bo = F(1) if n==0 else 2*b[n-1]+sum(b[k]*b[n-2-k] for k in range(n-1))
        assert even==ae; counts[0]+=1
        assert odd==bo; counts[1]+=1
        assert bo-ae==0; counts[2]+=1
        assert bo-(ae-a[n])==a[n]; counts[3]+=1
    print(counts,sum(counts))

if __name__ == "__main__":
    main()
