#!/usr/bin/env python3
"""Executable calibration for the concrete Syracuse parity-cylinder candidate.

This checks the exact one-step obligations consumed by
SyracuseParityCylinderCompilerExact.  It is calibration only: the general
Agda theorem remains theorem-bearing and is not inferred from this finite sweep.
"""
from itertools import product


def shortcut(x: int) -> int:
    return x // 2 if x % 2 == 0 else (3 * x + 1) // 2


def inv3(m: int) -> int:
    if m == 0:
        return 0
    return pow(3, -1, 1 << m)


def residue_candidate(word: tuple[int, ...]) -> int:
    r = 0
    level = 0
    for bit in reversed(word):
        level += 1
        modulus = 1 << level
        if bit == 0:
            r = (2 * r) % modulus
        else:
            r = (inv3(level) * (2 * r - 1)) % modulus
    return r


def main() -> None:
    for m in range(0, 11):
        modulus = 1 << m
        next_modulus = 1 << (m + 1)
        tails = list(product((0, 1), repeat=m))
        residues = [residue_candidate(tail) for tail in tails]
        assert len(set(residues)) == len(residues), (m, "candidate collision")

        for tail in tails:
            tail_residue = residue_candidate(tail)
            even_residue = residue_candidate((0,) + tail)
            odd_residue = residue_candidate((1,) + tail)

            assert even_residue % 2 == 0
            assert odd_residue % 2 == 1

            for lift in range(4):
                even_x = even_residue + lift * next_modulus
                if even_x == 0:
                    even_x += 4 * next_modulus
                assert even_x % 2 == 0
                assert shortcut(even_x) % modulus == tail_residue
                assert even_x % next_modulus == even_residue

                odd_x = odd_residue + lift * next_modulus
                if odd_x == 0:
                    odd_x += 4 * next_modulus
                assert odd_x % 2 == 1
                assert shortcut(odd_x) % modulus == tail_residue
                assert odd_x % next_modulus == odd_residue

    print("collatz syracuse one-step calibration: PASS (m <= 10)")


if __name__ == "__main__":
    main()
