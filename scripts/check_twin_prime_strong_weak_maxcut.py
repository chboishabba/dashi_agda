#!/usr/bin/env python3
"""Finite classical von Mangoldt correlation: reproducible max-cut stress test.

No infinitude or asymptotic assertions are inferred from these finite data.
The local prime sieve and the proper-power support are independent.
"""
import math

def trial(N):
    prime = bytearray(b'\x01') * (N + 1)
    prime[:2] = b'\0\0'
    for p in range(2, math.isqrt(N) + 1):
        if prime[p]:
            prime[p*p:N+1:p] = b'\0' * (((N-p*p)//p)+1)
    proper = set()
    lam = [0.] * (N + 1)
    for p in range(2, N + 1):
        if prime[p]:
            value = p
            while value <= N:
                lam[value] = math.log(p)
                if value != p:
                    proper.add(value)
                value *= p
    total = prime_only = error = 0.
    twins = 0
    for n in range(2, N - 1):
        weight = lam[n] * lam[n + 2]
        total += weight
        if prime[n] and prime[n + 2]:
            prime_only += weight
            twins += 1
        else:
            error += weight
    assert abs(total - prime_only - error) < 1e-7
    # Deliberately overcount base/exponent pairs: squares plus k>=3.
    bound = math.isqrt(N) + sum(int(N**(1/k))+1 for k in range(3, N.bit_length()))
    assert len(proper) <= bound
    assert error <= 2 * len(proper) * math.log(N)**2 + 1e-7
    return N, twins, len(proper), *(round(v/N, 6) for v in (total, prime_only, error))

if __name__ == "__main__":
    for N in (100, 1000, 10000, 100000, 300000):
        print(*trial(N))
