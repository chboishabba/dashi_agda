#!/usr/bin/env python3
"""Regression for generic literal Syracuse affine-word descent certificates.

Diagnostic only: finite execution never supplies the unbounded residual frontier.
"""


def shortcut(x: int) -> int:
    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2


def parity_prefix_and_iterate(x: int, depth: int) -> tuple[tuple[int, ...], int]:
    word: list[int] = []
    y = x
    for _ in range(depth):
        word.append(y & 1)
        y = shortcut(y)
    return tuple(word), y


def affine_coefficients(word: tuple[int, ...]) -> tuple[int, int, int]:
    """Return a,b,d with T^m(x)=(a*x+b)/d on the fixed parity word."""
    a, b, d = 1, 0, 1
    for bit in word:
        if bit == 0:
            d *= 2
        else:
            a, b, d = 3 * a, 3 * b + d, 2 * d
    return a, b, d


def minimum_certificate_start(word: tuple[int, ...]) -> int | None:
    a, b, d = affine_coefficients(word)
    gap = d - a
    if gap <= 0:
        return None
    return b // gap + 1


# Test the actual same-object implication, not independent random words.
for x in range(1, 50_001):
    for depth in range(1, 11):
        word, y = parity_prefix_and_iterate(x, depth)
        threshold = minimum_certificate_start(word)
        if threshold is not None and x >= threshold:
            assert y < x, (x, depth, word, threshold, y)

# Existing paid leaves become instances with sharper thresholds.
expected = {
    (1, 1, 0, 0): ((9, 5, 16), 1),
    (1, 1, 0, 1, 0): ((27, 23, 32), 5),
    (1, 1, 1, 0, 0): ((27, 19, 32), 4),
}
for word, (coefficients, threshold) in expected.items():
    assert affine_coefficients(word) == coefficients
    assert minimum_certificate_start(word) == threshold

# First uniformly killed descendants of the refined residual families at depth 7.
first_residual_kills = {
    (1, 1, 0, 1, 1, 0, 0): ((81, 85, 128), 2),
    (1, 1, 1, 0, 1, 0, 0): ((81, 73, 128), 2),
    (1, 1, 1, 1, 0, 0, 0): ((81, 65, 128), 2),
}
for word, (coefficients, threshold) in first_residual_kills.items():
    assert affine_coefficients(word) == coefficients
    assert minimum_certificate_start(word) == threshold

print("collatz syracuse generic word-certificate regression: PASS")
print("checked starts: 1..50000, depths: 1..10")
