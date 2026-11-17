#!/usr/bin/env python3
"""Independent SymPy exact-integer audit of the four-arctangent identity.

Only finite rational cyclotomic/Gaussian arithmetic is certified here.
Same-source Bishop arctangent addition and branch semantics remain open.
"""
from sympy import I, Integer, simplify
from fractions import Fraction
from check_bishop_fast_pi_binary_split import (
    MACHIN, FOUR_TERM, schedule, enclosure
)

z = ((Integer(57)+I)**44 * (Integer(239)+I)**7
     * (Integer(12943)+I)**24 / (Integer(682)+I)**12)
re, im = z.as_real_imag()
assert simplify(re-im) == 0
assert re > 0 and im > 0

for digits in (20, 100, 1000):
    a, b = enclosure(MACHIN, schedule(MACHIN, digits))
    c, d = enclosure(FOUR_TERM, schedule(FOUR_TERM, digits))
    assert a <= d and c <= b
    assert b-a <= Fraction(1, 10**digits)
    assert d-c <= Fraction(1, 10**digits)

print("PASS exact Gaussian identity and independently intersecting rational intervals")
print("WARNING not a proof of equality of the two constructed Bishop reals")
