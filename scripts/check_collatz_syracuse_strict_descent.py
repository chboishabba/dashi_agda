#!/usr/bin/env python3
"""Finite regression for the exact terminal strict-descent interface.

This is calibration only. It intentionally does not count as a general proof.
"""


def shortcut(x: int) -> int:
    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2


def first_strict_descent(x: int, cap: int = 1000):
    y = x
    for m in range(1, cap + 1):
        y = shortcut(y)
        if y < x:
            return m, y
    return None


max_horizon = 0
max_start = 1
for x in range(2, 200_000):
    witness = first_strict_descent(x)
    assert witness is not None, x
    m, _ = witness
    if m > max_horizon:
        max_horizon = m
        max_start = x

# The coarse affine-good-prefix sufficient route is strictly stronger than
# literal descent: 3 reaches a lower value at horizon 5, while 3^5 > 3.
assert first_strict_descent(3) == (5, 2)
assert 3**5 > 3

print("collatz syracuse strict-descent finite regression: PASS")
print("checked starts: 2..199999")
print("largest first-descent horizon:", max_horizon, "at", max_start)
