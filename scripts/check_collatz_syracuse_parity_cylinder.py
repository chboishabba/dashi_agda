#!/usr/bin/env python3

def syracuse(x: int) -> int:
    assert x > 0
    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2

def parity_word(x: int, m: int) -> tuple[int, ...]:
    out = []
    for _ in range(m):
        out.append(x & 1)
        x = syracuse(x)
    return tuple(out)

for m in range(0, 8):
    modulus = 1 << m
    word_to_residue: dict[tuple[int, ...], int] = {}
    for x in range(1, 1 + 8 * max(1, modulus)):
        word = parity_word(x, m)
        residue = x % modulus if modulus > 1 else 0
        previous = word_to_residue.setdefault(word, residue)
        assert previous == residue, (m, word, previous, residue)
    assert len(word_to_residue) == modulus
    assert len(set(word_to_residue.values())) == modulus

print('collatz parity-cylinder exhaustive specimens: PASS')
