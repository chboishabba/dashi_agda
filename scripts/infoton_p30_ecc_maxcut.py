#!/usr/bin/env python3
"""Reference Hsiao-type (72,64) SECDED, plus a NON-P30 radix-unit negative control.

This is not the original Infoton P30 encoder/verifier or physical hardware data.
"""
from dataclasses import dataclass
from itertools import combinations
from fractions import Fraction
import json

DATA = tuple(i for i in range(256) if i.bit_count() == 3) + \
       tuple(i for i in range(256) if i.bit_count() == 5)[:8]
PARITY = tuple(1 << i for i in range(8))
COLUMNS = DATA + PARITY
assert len(DATA) == 64 and len(set(COLUMNS)) == 72
assert all(v.bit_count() % 2 == 1 for v in COLUMNS)
INDEX = {v: i for i, v in enumerate(COLUMNS)}
MASK64 = 2 ** 64 - 1
UNITS = (1, 7, 11, 13, 17, 19, 23, 29)


def parity8(n):
    if not 0 <= n <= MASK64:
        raise ValueError("expected 64-bit value")
    s = 0
    for i, col in enumerate(DATA):
        if (n >> i) & 1:
            s ^= col
    return s


def encode72(n):
    return n | (parity8(n) << 64)


def syndrome(word):
    if not 0 <= word < 2**72:
        raise ValueError("expected 72-bit codeword")
    return parity8(word & MASK64) ^ (word >> 64)


@dataclass(frozen=True)
class Decoded:
    status: str
    data: int | None
    position: int | None


def decode72(word):
    s = syndrome(word)
    if s == 0:
        return Decoded("clean", word & MASK64, None)
    if s in INDEX:
        i = INDEX[s]
        return Decoded("single_corrected", (word ^ (1 << i)) & MASK64, i)
    return Decoded("detected_uncorrectable", None, None)


def encode_unit_surrogate(byte):
    """A deliberately small, NOT-authentic P30 codec to test membership claims."""
    if not 0 <= byte < 256:
        raise ValueError("expected a byte")
    return (UNITS[byte // 64], UNITS[byte // 8 % 8], UNITS[byte % 8])


def decode_unit_surrogate(symbols):
    if len(symbols) != 3 or any(v not in UNITS for v in symbols):
        return None
    a, b, c = (UNITS.index(v) for v in symbols)
    n = 64*a + 8*b + c
    return n if n < 256 else None


def reference_receipt():
    word = 0x0123456789abcdef
    encoded = encode72(word)
    assert syndrome(encoded) == 0
    for i in range(72):
        got = decode72(encoded ^ (1 << i))
        assert got.status == "single_corrected" and got.position == i and got.data == word
    for i, j in combinations(range(72), 2):
        got = decode72(encoded ^ (1 << i) ^ (1 << j))
        assert got.status == "detected_uncorrectable"
    undetected = detected = 0
    for v in range(256):
        old = encode_unit_surrogate(v)
        assert decode_unit_surrogate(old) == v
        for i in range(3):
            for other in UNITS:
                if other == old[i]:
                    continue
                modified = list(old)
                modified[i] = other
                result = decode_unit_surrogate(tuple(modified))
                if result is None:
                    detected += 1
                else:
                    assert result != v
                    undetected += 1
    assert (undetected, detected) == (4352, 1024)
    return dict(
        reference="Hsiao-type odd-column (72,64) SECDED",
        reference_single_bit_corrected=72,
        reference_double_bit_detected=2556,
        surrogate="P30-inspired unit membership, NOT the original P30 codec/verifier",
        surrogate_total_valid_position_substitutions=5376,
        surrogate_undetected=undetected,
        surrogate_detected=detected,
        surrogate_undetected_fraction=str(Fraction(undetected, 5376)),
        original_P30_ECC_equivalence_proven=False,
        hardware_energy_reduction_measured=False,
    )


def rack_projection(fixed_fraction, baseline_kw=Fraction(130),
                    operations_ratio=Fraction(12264, 163)):
    """Conditional toy model; neither P30 measurements nor a facility heat model."""
    return baseline_kw * (fixed_fraction + (1-fixed_fraction)/operations_ratio)


def rack_receipt():
    return {str(p): round(float(rack_projection(Fraction(p, 100))), 6)
            for p in (0, 5, 10, 25, 50, 75, 90, 100)}


if __name__ == "__main__":
    print(json.dumps({"ecc": reference_receipt(), "projected_rack_kw_by_fixed_percent": rack_receipt()}, indent=2))
