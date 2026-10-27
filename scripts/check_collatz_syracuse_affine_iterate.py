#!/usr/bin/env python3

def syracuse(x: int) -> int:
    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2

def parity_word(x: int, m: int) -> tuple[int, ...]:
    out = []
    for _ in range(m):
        out.append(x & 1)
        x = syracuse(x)
    return tuple(out)

def additive(word: tuple[int, ...]) -> int:
    if not word:
        return 0
    head, *tail_list = word
    tail = tuple(tail_list)
    tail_a = additive(tail)
    if head == 0:
        return 2 * tail_a
    return 3 ** sum(tail) + 2 * tail_a

for x in range(1, 201):
    y = x
    for m in range(0, 13):
        word = parity_word(x, m)
        lhs = (2 ** m) * y
        rhs = (3 ** sum(word)) * x + additive(word)
        assert lhs == rhs, (x, m, word, lhs, rhs)
        y = syracuse(y)

print('collatz affine-iterate exhaustive specimens: PASS')
