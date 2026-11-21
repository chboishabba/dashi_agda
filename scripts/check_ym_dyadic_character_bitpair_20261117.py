#!/usr/bin/env python3
"""Exact dyadic Fourier character cancellation with explicit bit-pair witnesses.

For N=2**s and 0<k<N, k=2**t*u with u odd. Set r=N//2**(t+1).
In Q[z]/(z**(N//2)+1), z**(k*r)=(-1)**u=-1.
The N terms z**(k*j) partition into adjacent blocks of length r,
whose terms cancel pairwise at offsets r. This is a universal
finite pairing argument, not a numerical/root-based approximation.

Attribution: original DASHI finite-character/Fourier theorem owners,
Fejer, Stroud, Pizzetti/Folland, Bishop/Bridges and Wilson/Balaban.
No claim of Agda acceptance or a physical continuum theorem.
"""
import argparse

def v2(k):
    assert k > 0
    t = 0
    while k % 2 == 0:
        k //= 2
        t += 1
    return t, k

def quotient_monomial(N, exponent):
    """Exact representative of z**exponent modulo z**(N//2)+1."""
    quotient, remainder = divmod(exponent, N//2)
    return remainder, -1 if quotient % 2 else 1

def check_character_pairing(N, k):
    assert N >= 2 and N & (N-1) == 0 and 0 < k < N
    t, u = v2(k)
    r = N // (2 ** (t+1))
    assert r * 2 ** (t+1) == N and u % 2 == 1
    assert k * r == u * (N//2)
    block_count = N // (2*r)
    assert block_count == 2**t
    checks = 0
    for block in range(block_count):
        for h in range(r):
            j = block*2*r + h
            a, va = quotient_monomial(N, k*j)
            b, vb = quotient_monomial(N, k*(j+r))
            assert a == b and va == -vb, (N,k,j,a,va,b,vb)
            checks += 1
    assert checks*2 == N
    return checks

def run(max_power):
    total = 0
    for s in range(1, max_power + 1):
        N = 1 << s
        for k in range(1, N):
            total += check_character_pairing(N, k)
        print(f"N={N}: paired all {N-1} nontrivial characters")
    print("YM_DYADIC_CHARACTER_PAIR_CERTIFICATE_PASS",total)

if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-power", type=int, default=8)
    args = ap.parse_args()
    assert 1 <= args.max_power <= 12
    run(args.max_power)
