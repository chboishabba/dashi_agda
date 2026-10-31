#!/usr/bin/env python3
"""Retained signed Fourier shells: rigorous identities, numerical diagnostics only.
Original dashiRTX ownership retained. No claim of prime-pair distribution.
"""
import math
import numpy as np

def run(X):
    M = 1 << (2 * X + 4).bit_length()
    prime = np.ones(X+1, dtype=bool)
    prime[:2] = False
    for p in range(2, math.isqrt(X)+1):
        if prime[p]:
            prime[p*p::p] = False
    f = np.zeros(M)
    for p in np.flatnonzero(prime):
        q = int(p)
        while q <= X:
            f[q] = math.log(int(p))
            q *= int(p)
    fft = np.fft.fft(f)
    k = np.arange(M)
    # Fixed transform convention F(k)=sum f(n) exp(-2pi i k n /M).
    signed = (np.abs(fft)**2 * np.exp(-4j*np.pi*k/M) / M).real
    direct = float(np.dot(f[:-2], f[2:]))
    assert abs(direct - signed.sum()) < 2e-7
    bands = []
    d = np.minimum(k,M-k)
    low=0
    while low <= M//2:
        high=1 if low == 0 else 2*low
        mask=(d>=low)&(d<high)
        if np.any(mask):
            bands.append((int(low),float(signed[mask].sum()),
                          float(np.abs(signed[mask]).sum())))
        low=high
    assert abs(sum(x[1] for x in bands)-direct) < 2e-7
    dc=float(signed[0])
    # A valid but normally useless universal lower bound.
    universal_lower=dc-sum(x[2] for x in bands if x[0]!=0)
    print(X, M, round(direct/X,8),round(dc/X,8),
          round((direct-dc)/X,8),round(universal_lower/X,8),
          round(sum(x[2] for x in bands)/X,8))
    return bands
if __name__=='__main__':
    print('X M S/X DC/X nonDC/X trivialLower/X absoluteShellBudget/X')
    for X in (100,1000,10000,100000):
        run(X)
