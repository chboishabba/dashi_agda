#!/usr/bin/env python3
"""Exact-rational bounded non-Cauchy example with O(1/k) increments.

Tests the E1 inference in the supplied proposed Yang--Mills gate proof:
|E_{k+1}-E_k| <= C/k is NOT a Cauchy theorem; regrouping indexes
without extra cancellation/summable control cannot create 2^-delta j.
No claim about the actual Wilson sequence is made.
"""
from fractions import Fraction

def sawtooth(k: int) -> Fraction:
    assert k >= 1
    stage = k.bit_length() - 1
    half = 1 << stage
    t = Fraction(k - half, half)
    return t if stage % 2 == 0 else 1 - t

def check(max_stage=17):
    for k in range(1, 1 << max_stage):
        step = abs(sawtooth(k+1) - sawtooth(k))
        assert step <= Fraction(2, k)
        assert Fraction(0) <= sawtooth(k) <= Fraction(1)
    for j in range(max_stage):
        assert sawtooth(1 << j) == (0 if j % 2 == 0 else 1)
        assert (1 << j) * Fraction(1, 1 << (j+1)) == Fraction(1,2)
        assert all(k <= (1 << (j+1)) for k in range(1 << j, 1 << (j+1)))
    # Stronger failure of "just group the one-step O(1/k) errors".
    # The 4^j subsequence is identically ZERO (hence Cauchy with
    # vanishing differences and any claimed 2^(-delta*j) error),
    # while the 2*4^j intermediate points are identically ONE.
    # Thus even a perfectly convergent sparse geometric subsequence
    # and the original one-step O(1/k) estimate do NOT imply
    # convergence/tightness of the full UV cutoff family.
    dyadic_pairs = []
    for j in range((max_stage - 1) // 2):
        left = 1 << (2*j)
        midpoint = 1 << (2*j+1)
        right = 1 << (2*j+2)
        assert right <= (1 << max_stage)
        assert sawtooth(left) == 0
        assert sawtooth(midpoint) == 1
        assert sawtooth(right) == 0
        assert abs(sawtooth(right)-sawtooth(left)) == 0
        assert abs(sawtooth(midpoint)-sawtooth(left)) == 1
        dyadic_pairs.append((left, midpoint, right))

    # Explicit harmonic block estimate: without actual cancellation,
    # the sum of 1/k over a whole dyadic interval is >= 1/2.
    # Passing from k to 2k cannot be bounded by O(1/k) merely by
    # plugging in the ENDPOINT's single-step error.
    for j in range(max_stage):
        low = 1 << j
        upper = low << 1
        assert sum((Fraction(1, k) for k in range(low, upper)),
                   Fraction(0)) >= Fraction(1, 2)

    print(f'PASS exact bounded rational sawtooth: {2**max_stage - 1} adjacent O(1/k) bounds')
    print(f'PASS {max_stage} alternating dyadic stage values 0/1 and harmonic-block lower bound 1/2')
    print(f'PASS {len(dyadic_pairs)} exact 4^j-subsequence zero/one/zero counterexamples')
    print('NO-GO: even geometric-subsequence convergence alone does not force full E1 Cauchy')
    print('CONCLUSION: an O(1/k) one-step bound does NOT imply E1 Cauchy convergence.')

if __name__ == '__main__':
    check()
