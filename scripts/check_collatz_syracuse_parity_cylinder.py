#!/usr/bin/env python3

from itertools import product


def syracuse(x: int) -> int:
    assert x > 0
    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2


def parity_word(x: int, m: int) -> tuple[int, ...]:
    out = []
    for _ in range(m):
        out.append(x & 1)
        x = syracuse(x)
    return tuple(out)


def inv3_candidate(m: int) -> int:
    if m == 0:
        return 0
    if m == 1:
        return 1
    if m == 2:
        return 3
    return 4 * inv3_candidate(m - 2) - 1


def residue_candidate(word: tuple[int, ...]) -> int:
    if not word:
        return 0
    bit, *tail_list = word
    tail = tuple(tail_list)
    m = len(word)
    modulus = 1 << m
    r = residue_candidate(tail)
    if bit == 0:
        return (2 * r) % modulus
    return (inv3_candidate(m) * ((2 * r + modulus) - 1)) % modulus


for m in range(0, 13):
    modulus = 1 << m

    if m > 0:
        assert (3 * inv3_candidate(m)) % modulus == 1 % modulus

    # The recursive candidate itself is a permutation of the level-m residues.
    candidates: dict[tuple[int, ...], int] = {}
    for word in product((0, 1), repeat=m):
        candidate = residue_candidate(word)
        assert 0 <= candidate < modulus
        candidates[word] = candidate
        if word and word[0] == 1:
            tail_residue = residue_candidate(word[1:])
            assert (3 * candidate + 1) % modulus == (2 * tail_residue) % modulus

    assert len(candidates) == modulus
    assert len(set(candidates.values())) == modulus

    # Same-object check against literal Syracuse starts over several whole blocks.
    for x in range(1, 1 + 4 * max(1, modulus)):
        word = parity_word(x, m)
        observed_residue = x % modulus if modulus > 1 else 0
        assert observed_residue == residue_candidate(word), (
            m,
            x,
            word,
            observed_residue,
            residue_candidate(word),
        )

print('collatz parity-cylinder candidate/classification through m<=12: PASS')
