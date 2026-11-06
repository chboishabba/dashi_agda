#!/usr/bin/env python3
"""Independent bounded Conway rule-rewrite and gamma syntax regression.

This is NOT an Agda kernel proof. Never materialize giant Conway values.
"""
import itertools
from functools import lru_cache

CAP = 100000

class TooLarge(Exception):
    pass

def power(a, b):
    if b > 100000 or (a > 1 and b > 30):
        raise TooLarge
    x = a ** b
    if x > CAP:
        raise TooLarge
    return x

def iterate(f, count, seed):
    if count > CAP:
        raise TooLarge
    for _ in range(count):
        seed = f(seed)
        if seed > CAP:
            raise TooLarge
    return seed

def prefix_value(chain):
    if not chain:
        return 1
    v = chain[0]
    ext = lambda n: power(chain[0], n)
    for p in chain[1:]:
        old_v, old_ext = v, ext
        v = old_ext(p)
        def make_F(value, extension):
            def F(q, pen):
                if q == 1:
                    return extension(pen)
                if pen == 1:
                    return value
                if q < 1 or pen < 1:
                    raise ValueError
                return iterate(lambda x: F(q - 1, x), pen - 1, value)
            return F
        F = make_F(old_v, old_ext)
        ext = lambda q, F=F, p=p: F(q, p)
    return v

@lru_cache(None)
def rule_rewrite(chain):
    if not chain:
        return 1
    if len(chain) == 1:
        return chain[0]
    if len(chain) == 2:
        return power(*chain)
    if chain[-1] == 1:
        return rule_rewrite(chain[:-1])
    for i in range(1, len(chain) - 1):
        if chain[i] == 1:
            return rule_rewrite(chain[:i])
    prefix, p, q = chain[:-2], chain[-2], chain[-1]
    inner = rule_rewrite(prefix + (p - 1, q))
    return rule_rewrite(prefix + (inner, q - 1))

def gamma(n):
    bits = bin(n + 1)[2:]
    return "0" * (len(bits) - 1) + bits

def read_gamma(word, pos):
    k = 0
    while pos + k < len(word) and word[pos + k] == "0":
        k += 1
    end = pos + 2 * k + 1
    if end > len(word):
        raise ValueError("truncated gamma")
    return int(word[pos + k:end], 2) - 1, end

def encode(nums):
    return gamma(len(nums)) + "".join(map(gamma, nums))

def decode(bits):
    n, pos = read_gamma(bits, 0)
    out = []
    for _ in range(n):
        value, pos = read_gamma(bits, pos)
        out.append(value)
    if pos != len(bits):
        raise ValueError("trailing bits")
    return tuple(out)

def main():
    count = skipped = 0
    for length in range(5):
        for items in itertools.product((1, 2, 3), repeat=length):
            try:
                assert prefix_value(items) == rule_rewrite(items), items
                count += 1
            except (TooLarge, RecursionError, OverflowError):
                skipped += 1
    assert prefix_value((2, 3, 2)) == 16
    assert prefix_value((3, 2, 2)) == 27
    assert prefix_value((2, 2, 2, 2)) == 4
    assert prefix_value((3, 1, 2, 3)) == 3

    roundtrips = 0
    for n in range(5):
        for xs in itertools.product(range(5), repeat=n):
            assert decode(encode(xs)) == xs
            assert len(encode(xs)) == len(gamma(n)) + sum(len(gamma(v)) for v in xs)
            try:
                decode(encode(xs) + "0")
                raise AssertionError(("accepted trailing bit", xs))
            except ValueError:
                pass
            roundtrips += 1
    canonical = rejected = 0
    for bits_count in range(13):
        for value in range(1 << bits_count):
            word = format(value, f"0{bits_count}b") if bits_count else ""
            try:
                source = decode(word)
                assert encode(source) == word
                canonical += 1
            except ValueError:
                rejected += 1
    assert canonical == 133 and rejected == 8058
    print(f"Conway reference: {count} agreement, {skipped} bounded skips; gamma: {roundtrips} roundtrips; exhaustive <=12-bit: {canonical} canonical, {rejected} rejected")

if __name__ == "__main__":
    main()
