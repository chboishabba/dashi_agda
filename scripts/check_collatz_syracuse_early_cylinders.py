#!/usr/bin/env python3
"""Regression for the exact early survivor-cylinder pruning.

Diagnostic only: the Agda owners carry the theorem.  This independently checks
word orientation, affine corrections, the x>=8 margins, and the depth-five
partition used by CollatzSyracuseEarlyCylinderEliminationExact.
"""


def affine(word: str) -> tuple[int, int]:
    """Return (3^ones, additive correction) for 2^m T^m(x)."""
    count = 0
    correction = 0
    for bit in reversed(word):
        if bit == "0":
            correction *= 2
        elif bit == "1":
            correction = 3**count + 2 * correction
            count += 1
        else:
            raise ValueError(bit)
    return 3**count, correction


def uniform_below(word: str, cutoff: int) -> bool:
    odd_scale, correction = affine(word)
    dyadic = 2 ** len(word)
    return odd_scale * cutoff + correction < dyadic * cutoff


assert affine("1100") == (9, 5)
assert affine("11010") == (27, 23)
assert affine("11100") == (27, 19)

for word in ("1100", "11010", "11100"):
    assert uniform_below(word, 8), word
    for x in range(8, 10_000):
        p, a = affine(word)
        assert p * x + a < (2 ** len(word)) * x

# Starting from the already-paid 11 tail, prune exactly the three uniform
# leaves used by the Agda compiler.  Remaining depth-five families are the
# explicit 11011 / 11101 leaves plus the unresolved 1111 prefix family.
paid = {"1100", "11010", "11100"}
residual_depth5 = {
    word
    for word in ("".join(bits) for bits in __import__("itertools").product("01", repeat=5))
    if word.startswith("11")
    and not any(word.startswith(prefix) for prefix in paid)
}
assert residual_depth5 == {"11011", "11101", "11110", "11111"}
assert {word[:4] if word.startswith("1111") else word for word in residual_depth5} == {
    "11011",
    "11101",
    "1111",
}

print("collatz syracuse early-cylinder regression: PASS")
print("paid prefixes: 1100, 11010, 11100")
print("residual families: 11011, 11101, 1111...")
