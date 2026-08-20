#!/usr/bin/env python3
"""Exact finite verification of the optimal-width T^9 locality construction.

This script checks the explicit 3-trit -> 5-bit codec formalized in
`DASHI.Foundations.TernaryNineOptimalBinaryDilationExact` and its three-block
product lift.

Results:
  * 27 block states map injectively into 32 five-bit words;
  * all 54 forward nearest-neighbour block edges have Hamming distance <= 2;
  * the exact edge profile is 19 distance-one + 35 distance-two edges;
  * three independent blocks give an injective 3^9 -> 2^15 codec;
  * every primitive nearest-neighbour transition in T^9 changes <= 2 bits;
  * one-bit locality at the all-centre state is impossible because 18 > 15.

The last line is a degree/pigeonhole lower bound, not a hardware timing claim.
Together with the explicit upper codec it establishes the declared finite
storage/locality optimum: optimal-width 15-bit storage with dilation two.
"""

from itertools import product

TRITS = (0, 1, 2)  # semantic -1, 0, +1

BLOCK = {
    (0, 0, 0): 0b10110,
    (0, 0, 1): 0b00100,
    (0, 0, 2): 0b00101,
    (0, 1, 0): 0b10000,
    (0, 1, 1): 0b00001,
    (0, 1, 2): 0b00111,
    (0, 2, 0): 0b10010,
    (0, 2, 1): 0b10011,
    (0, 2, 2): 0b10101,
    (1, 0, 0): 0b01110,
    (1, 0, 1): 0b00010,
    (1, 0, 2): 0b00011,
    (1, 1, 0): 0b01000,
    (1, 1, 1): 0b00000,
    (1, 1, 2): 0b00110,
    (1, 2, 0): 0b11000,
    (1, 2, 1): 0b10001,
    (1, 2, 2): 0b10100,
    (2, 0, 0): 0b01011,
    (2, 0, 1): 0b01010,
    (2, 0, 2): 0b01111,
    (2, 1, 0): 0b01101,
    (2, 1, 1): 0b01001,
    (2, 1, 2): 0b01100,
    (2, 2, 0): 0b11100,
    (2, 2, 1): 0b11001,
    (2, 2, 2): 0b11101,
}


def hamming(left: int, right: int) -> int:
    return (left ^ right).bit_count()


def block_edges():
    for state in product(TRITS, repeat=3):
        for coordinate in range(3):
            if state[coordinate] < 2:
                target = list(state)
                target[coordinate] += 1
                yield state, tuple(target)


def encode9(state: tuple[int, ...]) -> int:
    """Concatenate the three 5-bit block words into one 15-bit word."""
    assert len(state) == 9
    a = BLOCK[state[0:3]]
    b = BLOCK[state[3:6]]
    c = BLOCK[state[6:9]]
    return (a << 10) | (b << 5) | c


def nine_edges():
    for state in product(TRITS, repeat=9):
        for coordinate in range(9):
            if state[coordinate] < 2:
                target = list(state)
                target[coordinate] += 1
                yield state, tuple(target)


def main() -> None:
    assert len(BLOCK) == 27
    assert len(set(BLOCK.values())) == 27
    assert all(0 <= word < 32 for word in BLOCK.values())

    profile = {1: 0, 2: 0}
    block_max = 0
    for left, right in block_edges():
        distance = hamming(BLOCK[left], BLOCK[right])
        assert distance <= 2
        profile[distance] += 1
        block_max = max(block_max, distance)

    assert profile == {1: 19, 2: 35}
    assert block_max == 2

    all_states = tuple(product(TRITS, repeat=9))
    images = [encode9(state) for state in all_states]
    assert len(images) == 3**9 == 19683
    assert len(set(images)) == 3**9
    assert all(0 <= word < 2**15 for word in images)

    nine_max = 0
    edge_count = 0
    for left, right in nine_edges():
        distance = hamming(encode9(left), encode9(right))
        assert distance <= 2
        nine_max = max(nine_max, distance)
        edge_count += 1

    assert nine_max == 2
    assert edge_count == 9 * 2 * 3**8

    # Degree obstruction at the all-centre state of P3^9.
    ternary_centre_degree = 2 * 9
    binary_one_bit_directions = 15
    assert ternary_centre_degree == 18
    assert binary_one_bit_directions == 15
    assert ternary_centre_degree > binary_one_bit_directions

    assert 2**14 < 3**9 <= 2**15
    assert 2**15 - 3**9 == 13085

    print("block states:", len(BLOCK))
    print("block edge profile:", profile)
    print("block dilation:", block_max)
    print("T^9 states:", len(images))
    print("T^9 primitive edges:", edge_count)
    print("15-bit product-code dilation:", nine_max)
    print("dilation-one centre obstruction:", ternary_centre_degree, ">", binary_one_bit_directions)
    print("unused 15-bit codewords:", 2**15 - 3**9)
    print("RESULT: declared optimal-width T^9 nearest-transition dilation = 2")


if __name__ == "__main__":
    main()
