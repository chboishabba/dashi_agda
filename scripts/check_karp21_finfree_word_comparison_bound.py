#!/usr/bin/env python3
"""Independent N21 bound regression (not an Agda kernel proof).

Original source statements:
  twoPerEdge(m) <= |gamma graph word| for every successful parse;
  full-history address-comparison count C(m)=2m(m-1).
This tests the arithmetic implication against all bounded m,L.
"""

def gamma(n: int) -> str:
    bits = bin(n + 1)[2:]
    return "0" * (len(bits) - 1) + bits

def comparison_count(m: int) -> int:
    count = 0
    for j in range(m):
        count += 4 * j
    return count

def check() -> None:
    count = 0
    for word_bits in range(501):
        for edges in range(word_bits // 2 + 1):
            exact = comparison_count(edges)
            assert exact == 2 * edges * max(edges - 1, 0)
            assert edges <= 2 * edges <= word_bits
            assert exact <= comparison_count(word_bits)
            assert exact <= 2 * (word_bits ** 2)
            count += 1
    assert count == 63001, count
    huge_n = 2 ** 1024
    assert len(gamma(huge_n)) < 4096
    assert comparison_count(1) == 0
    assert comparison_count(2) == 4
    print(
        "PASS N21 comparison-count: "
        f"{count} (m,L) pairs, n=2^1024 compact gamma control"
    )

if __name__ == "__main__":
    check()
