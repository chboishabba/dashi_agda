#!/usr/bin/env python3
"""P0-B/F original unsigned gamma -> bit-native LE endpoint + strict validator.

Literal scanners mirror Native.readGammaBinary + Positive.predecessorLE;
the strict graph edge validator mirrors the source u<v<n and lexical
strictAfter over binary addresses. This is finite differential evidence,
not an Agda kernel check or physical bit-Turing-machine clock.
"""
from itertools import product
from random import Random


def gamma_scan(bits):
    k = 0
    while k < len(bits) and not bits[k]:
        k += 1
    if k >= len(bits) or len(bits) < 2*k+1:
        return None
    return bits[k:2*k+1], bits[2*k+1:]


def unsigned_endpoint(bits):
    parsed = gamma_scan(bits)
    if parsed is None:
        return None
    successor, suffix = parsed
    le = tuple(reversed(successor))
    out = []
    borrow = 1
    for bit in le:
        if borrow and bit:
            out.append(False)
            borrow = 0
        elif borrow:
            out.append(True)
        else:
            out.append(bit)
    return tuple(out), suffix


def value_le(bits):
    return sum(int(bit) << i for i, bit in enumerate(bits))


def original_gamma(bits):
    parsed = gamma_scan(bits)
    if parsed is None:
        return None
    successor, suffix = parsed
    result = 0
    for bit in successor:
        result = 2*result + int(bit)
    return result-1, suffix


def compare_le(a, b):
    ordering = 0
    for i in range(max(len(a), len(b))):
        x = a[i] if i < len(a) else False
        y = b[i] if i < len(b) else False
        if x != y:
            ordering = 1 if x else -1
    return ordering


def value_bits(n, padding=0):
    return tuple(bool((n >> i) & 1) for i in range(n.bit_length()+padding))


def valid_binary(n, edges):
    previous = None
    for u, v, _weight in edges:
        if not(compare_le(u, v) < 0 and compare_le(v, n) < 0):
            return False
        if previous is not None:
            a,b = previous
            if not (compare_le(a,u)<0 or
                    (compare_le(a,u)==0 and compare_le(b,v)<0)):
                return False
        previous = (u,v)
    return True


def valid_original(n, edges):
    previous = None
    for u,v,_w in edges:
        if not(u < v < n and (previous is None or (u,v)>previous)):
            return False
        previous = (u,v)
    return True


def main():
    cases = 0
    for size in range(17):
        for word in product((False, True), repeat=size):
            got = unsigned_endpoint(word)
            expected = original_gamma(word)
            assert (None if got is None else (value_le(got[0]),got[1])) == expected
            cases += 1
    rng = Random(1972)
    for size in (32, 64, 128, 256, 512, 1024):
        for _ in range(200):
            payload = tuple(bool(rng.getrandbits(1)) for _ in range(size))
            word = (False,)*size + (True,) + payload
            word += tuple(bool(rng.getrandbits(1)) for _ in range(rng.randrange(8)))
            got=unsigned_endpoint(word)
            assert got is not None and len(got[0])==size+1
            assert (value_le(got[0]),got[1]) == original_gamma(word)
            cases+=1
    edges_checked=0
    for n in range(18):
        for size in range(6):
            for _ in range(180):
                edges=[(rng.randrange(24),rng.randrange(24),rng.randrange(-32,32))
                       for _ in range(size)]
                binary_edges=[
                    (value_bits(u,rng.randrange(3)),
                     value_bits(v,rng.randrange(3)),w)
                    for u,v,w in edges]
                assert valid_binary(value_bits(n,rng.randrange(3)),binary_edges) == valid_original(n,edges)
                edges_checked+=1
    print(f'Original gamma and bit-native endpoint numerical/suffix differential: {cases:,} PASS')
    print(f'Original strict raw-edge validation vs bit-only validator: {edges_checked:,} PASS')
    print('Source regression only: no Agda kernel or bit-tape runtime receipt.')


if __name__=="__main__":
    main()
