#!/usr/bin/env python3
"""Finite exact CRT refinement and six-wheel candidate audit.

Distinct from proof: local execution is NOT an Agda kernel proof,
prime-gap theorem, or global distribution estimate.
Historical roots: CRT, Eratosthenes, Brun, Hardy--Littlewood.
Repository donors: PrimeModSixSieveExact, FinitePrimeProductSieveExact,
SSP369TreeAutomorphism, NatPrimeCountingInstance.
"""
from __future__ import annotations
from math import gcd, isqrt, prod

SSP15 = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71)


def is_prime(n: int) -> bool:
    return n >= 2 and all(n % d != 0 for d in range(2, isqrt(n)+1))


def six_wheel_candidates(bound: int) -> list[int]:
    return ([2] if bound >= 2 else []) + ([3] if bound >= 3 else []) + [
        n for n in range(4, bound + 1) if n % 6 in (1,5)
    ]


def certified_primes(bound: int) -> list[int]:
    # The 6-wheel is only a necessary filter. Actual primality is checked.
    return [n for n in six_wheel_candidates(bound) if is_prime(n)]


def local_pair_residues(p: int) -> list[int]:
    assert is_prime(p), (p, "a prime certificate is required")
    return [r for r in range(p) if r % p and (r+2) % p]


def crt_merge_one(r: int, M: int, t: int, p: int) -> int:
    assert gcd(M, p) == 1
    assert 0 <= r < M and 0 <= t < p
    # Unique x modulo M*p with x mod M=r and x mod p=t.
    k = ((t-r) * pow(M, -1, p)) % p
    x = r + M*k
    assert 0 <= x < M*p and x % M == r and x % p == t
    return x


def extend_pair_crt(M: int, residues: list[int], p: int) -> tuple[int,list[int]]:
    assert is_prime(p) and gcd(M,p) == 1
    local = local_pair_residues(p)
    extended = [crt_merge_one(r,M,t,p) for r in residues for t in local]
    assert len(set(extended)) == len(extended) == len(residues) * len(local)
    assert all(gcd(x*(x+2),M*p) == 1 for x in extended)
    return M*p, sorted(extended)


def run() -> None:
    for B in (3,6,30,71,100,251):
        generated=certified_primes(B)
        reference=[n for n in range(2,B+1) if is_prime(n)]
        assert generated == reference
        assert all(n<=3 or n%6 in (1,5) for n in reference)
    extended=[p for p in certified_primes(103) if p not in SSP15]
    assert (37,43,53,61,67,73,79,83,89,97,101,103) == tuple(extended)
    assert all(not is_prime(n) for n in (25,35,49,55,65,77,85,91,95))

    for p in certified_primes(103):
        residues=local_pair_residues(p)
        assert len(residues) == p-(1 if p==2 else 2)
        for n in range(0, min(3*p,330)):
            assert (n%p in residues) == ((n+p)%p in residues)
            assert ((n%p in residues) == ((n%p!=0) and ((n+2)%p!=0)))

    # Beginning at the literal {2,3} wheel: 1 valid residue 5 mod 6.
    M,residues=6,[5]
    for p in (5,7,11,13):
        M,residues=extend_pair_crt(M,residues,p)
        assert residues == [r for r in range(M) if gcd(r*(r+2),M)==1]
        assert len(residues)==prod(q-(1 if q==2 else 2) for q in (2,3,5,7,11,13) if q<=p)
    assert M==30030 and len(residues)==1485

    # New certified prime axes absent from the SSP15 basis.
    for p in (37,43,53,61,67,73,79,83,89,97,101,103):
        assert p not in SSP15
        M,new=extend_pair_crt(6,[5],p)
        assert M==6*p and len(new)==p-2
        assert new==[r for r in range(M) if gcd(r*(r+2),M)==1]

    M,rs=extend_pair_crt(6,[5],37)
    M,rs=extend_pair_crt(M,rs,43)
    assert M==6*37*43 and len(rs)==35*41==1435
    assert rs==[r for r in range(M) if gcd(r*(r+2),M)==1]

    n=43*53
    assert gcd(n*(n+2),prod(SSP15))==1 and not is_prime(n)
    print("Prime generation: 6-wheel candidates exactly cover certified primes <=251")
    print("Prime axes outside SSP15: 12 certified primes <=103")
    print("Local modular +p periodicity verified for every prime <=103")
    print("Arbitrary-prime CRT extension: modulus 30030 -> 1485 survivors")
    print("Outside SSP15: modulus 6*37*43=9546 -> 1435 survivors")
    print("All calculations exact integer checks; no unbounded prime-gap proof")


if __name__ == '__main__':
    run()
