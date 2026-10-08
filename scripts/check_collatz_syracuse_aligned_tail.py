#!/usr/bin/env python3
"""Executable calibration for the aligned-block literal Syracuse tail theorem.

This is deliberately only a regression/calibration.  The theorem-bearing proof
lives in DASHI/Analysis/CollatzSyracuseAlignedBlockTailExact.agda.
"""


def shortcut_syracuse(x: int) -> int:
    assert x > 0
    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2


def iterate(x: int, steps: int) -> int:
    for _ in range(steps):
        x = shortcut_syracuse(x)
    return x


def parity_word(x: int, steps: int) -> tuple[int, ...]:
    bits: list[int] = []
    for _ in range(steps):
        bits.append(x & 1)
        x = shortcut_syracuse(x)
    return tuple(bits)


def good_word(bits: tuple[int, ...]) -> bool:
    return 2 * (3 ** sum(bits)) <= 2 ** len(bits)


def first_threshold_block(steps: int) -> int:
    width = 2**steps
    return (3**steps + width - 1) // width


def check_case(n: int) -> None:
    steps = 8 * n + 1
    width = 2**steps
    block = first_threshold_block(steps)
    assert 3**steps <= block * width

    starts = range(block * width + 1, (block + 1) * width + 1)
    seen_words: set[tuple[int, ...]] = set()
    non_descent = 0
    bad_words = 0

    for x in starts:
        word = parity_word(x, steps)
        seen_words.add(word)
        bad = not good_word(word)
        if bad:
            bad_words += 1
        if iterate(x, steps) >= x:
            non_descent += 1
            assert bad, (n, x, word)

    # The aligned block is an exact parity-word bijection.
    assert len(seen_words) == width
    assert non_descent <= bad_words

    # The discrete five-eighths Chernoff consequence transported to starts.
    assert (2 ** (5 * n + 1)) * non_descent <= 3**steps


for n in range(3):
    check_case(n)

print("collatz aligned-block literal tail calibration: PASS")
