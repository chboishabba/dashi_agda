#!/usr/bin/env python3
"""Independent executable M16 finite TwinPrimeAt <-> count-change regression.

Two distinct algorithms: exact Eratosthenes prime counts versus trial-division
twin primality. No unbounded/analytic conclusion from finite execution.
DASHI prior owner: TwinPrimeCertifiedEnumeratorExact/PrimeCountingFunction.
"""
from math import isqrt

def trial_prime(n):
    return n >= 2 and all(n % d for d in range(2, isqrt(n) + 1))

def main():
    limit=70000
    sieve=[True]*(limit+3)
    sieve[0]=sieve[1]=False
    for p in range(2,isqrt(limit+2)+1):
        if sieve[p]:
            for multiple in range(p*p,limit+3,p):
                sieve[multiple]=False
    count=0
    jumps=[]
    for n in range(limit+1):
        old=count
        if n>=2 and sieve[n] and sieve[n+2]:
            count += 1
        change=count != old
        actual=trial_prime(n) and trial_prime(n+2)
        assert change == actual, (n,change,actual)
        if change:jumps.append(n)
    assert jumps[:6] == [3,5,11,17,29,41]
    print({"status":"PASS","tested_n":limit+1,
           "finite_twin_count_jumps":len(jumps),"first_six":jumps[:6],
           "unbounded_count_growth_proved":False,"agda_kernel_checked":False})
if __name__ == "__main__":
    main()
