#!/usr/bin/env python3
"""Independent exhaustive reference for the original Karp binary ripple adder.

Check all little-endian word pairs of widths 0..7.
This validates finite behavior, not Agda kernel acceptance.
"""
from itertools import product

def full_adder(a, b, carry):
    total = a + b + carry
    return total % 2, total // 2

def add_carry(xs, ys, carry=0):
    if not xs and not ys:
        return [1] if carry else []
    x, y = (xs[0] if xs else 0), (ys[0] if ys else 0)
    summand, next_carry = full_adder(x, y, carry)
    return [summand] + add_carry(xs[1:], ys[1:], next_carry)

def numeric(bits):
    return sum(bit << i for i, bit in enumerate(bits))

def counted_steps(xs, ys):
    return 1 if not xs and not ys else 1 + counted_steps(xs[1:], ys[1:])

def main():
    cases = 0
    for width_x in range(8):
        for width_y in range(8):
            for xs in product((0, 1), repeat=width_x):
                for ys in product((0, 1), repeat=width_y):
                    assert numeric(add_carry(xs, ys)) == numeric(xs) + numeric(ys)
                    assert counted_steps(xs, ys) <= 1 + width_x + width_y
                    cases += 1
    assert cases == 65025
    print(f"PASS {cases} all-pairs numeric+linear clock references")

if __name__ == "__main__":
    main()
