#!/usr/bin/env python3
"""Exact finite reference for Karp21BinaryWordEqualityPrimitiveExact.

This is an independent exhaustive finite regression, not Agda typechecking.
Checks all 16,129 pairs of bitwords with lengths zero through six.
"""
from itertools import product

def recursive_equal(left, right):
    if not left or not right:
        return len(left) == len(right)
    return (left[0] == right[0]) and recursive_equal(left[1:], right[1:])

def inspection_count(left, right):
    if not left or not right:
        return 1
    return 1 + inspection_count(left[1:], right[1:])

def main():
    total = 0
    for length_left in range(7):
        for length_right in range(7):
            for left in product((False, True), repeat=length_left):
                for right in product((False, True), repeat=length_right):
                    assert recursive_equal(left, right) == (left == right)
                    assert inspection_count(left, right) == min(len(left), len(right)) + 1
                    assert inspection_count(left, right) <= len(left) + 1
                    total += 1
    assert total == 16129
    print(f"PASS: {total} bit-word comparator soundness and exact count cases")

if __name__ == "__main__":
    main()
