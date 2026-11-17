#!/usr/bin/env python3
"""Exact finite oracle for M14 exhaustive support-case constructor.
Ordinary prime exponent=1, proper p^k exponent>=2, outside all.
All nine pair categories are tested; none imply an analytic theorem.
"""
from math import isqrt
from collections import Counter

def support(n):
    if n < 2: return "outside"
    for p in range(2,isqrt(n)+1):
        if n % p: continue
        k=n; exponent=0
        while k%p==0:
            k//=p; exponent+=1
        return ("prime" if exponent==1 else "proper") if k==1 else "outside"
    return "prime"

def main():
    freq=Counter((support(n),support(n+2)) for n in range(100000))
    assert sum(freq.values())==100000
    assert len(freq)==9
    assert support(25)=="proper" and support(27)=="proper"
    assert 25==5**2 and 27==3**3
    assert support(59)=="prime" and support(61)=="prime"
    assert support(209)=="outside" and support(329)=="outside"
    print({"status":"PASS","pairs":100000,"pair_cases":dict(freq),
           "proper_gap_two_25_27":True,
           "analytic_prime_power_error_bound_proved":False})
if __name__ == "__main__":
    main()
