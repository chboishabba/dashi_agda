#!/usr/bin/env python3
"""Reproducible, source-bounded Infoton P30 audit (stdlib only).

This is NOT a P30 implementation: no complete original P30 codec, syndrome,
operation-cost model, or hardware measurements were supplied in the 34-page
Walker PDF. The functions test universal claims and provide neutral comparators.
"""
from __future__ import annotations

import argparse
from decimal import Decimal, getcontext
from fractions import Fraction
from math import gcd
import json
import random
import zlib

getcontext().prec = 52
K_B = Decimal('1.380649e-23')
C = Decimal(299792458)
H = Decimal('6.62607015e-34')
E_CHARGE = Decimal('1.602176634e-19')
LN2 = Decimal(2).ln()

# Source: Walker, "NISTIR 6025 Information Physics Mapping", pdf pp. 29-31,
# https://infoton.ai/infoton-p30; these figures are source REPORTED.
SOURCE = {
    'utf8_bytes': 163,
    'p30_positions_char': 167,
    'p30_char_roundtrip_bytes': 167,
    'p30_packed_roundtrip_bytes': 171,
    'p30_direct_packed_write_only_bytes': 116,
    'huffman_payload_only_bytes': 103,
    'huffman_roundtrip_total_bytes': 533,
    'ecc_verified_operations': 12264,
    'p30_ingress_only_operations': 163,
    'conventional_rack_kw': 130,
}


def coprime_residues(base: int) -> tuple[int, ...]:
    if base < 2:
        raise ValueError('base >= 2 required')
    return tuple(i for i in range(base) if gcd(i, base) == 1)


def min_digits_for_alphabet(states: int, radix: int) -> int:
    if radix < 2 or states < 1:
        raise ValueError('radix >= 2, states >= 1 required')
    d, capacity = 0, 1
    while capacity < states:
        d += 1
        capacity *= radix
    return d


def theoretical_fixed_digits_bits(radix: int, digits: int) -> int:
    """Smallest number of fixed binary bits to identify ALL radix**digits states."""
    if radix < 2 or digits < 0:
        raise ValueError('invalid radix/digits')
    return (pow(radix, digits) - 1).bit_length()


def radix_encode(payload: bytes, radix: int) -> tuple[int, tuple[int, ...]]:
    """Exact integer-to-base-radix encoding; explicit length preserves zero bytes."""
    if radix < 2:
        raise ValueError('radix >= 2 required')
    n = int.from_bytes(payload, 'big')
    ds = []
    while n:
        n, r = divmod(n, radix)
        ds.append(r)
    return len(payload), tuple(reversed(ds))


def radix_decode(encoded: tuple[int, tuple[int, ...]], radix: int) -> bytes:
    size, digits = encoded
    if radix < 2 or size < 0 or any(d < 0 or d >= radix for d in digits):
        raise ValueError('invalid encoded value')
    n = 0
    for d in digits:
        n = n * radix + d
    if n >= 256 ** size:
        raise ValueError('payload overflows declared byte length')
    return n.to_bytes(size, 'big')


def is_valid_coprime_position(position: int) -> bool:
    return 0 <= position < 30 and gcd(position, 30) == 1


def toggle(bit: int) -> int:
    if bit not in (0, 1):
        raise ValueError('binary state required')
    return bit ^ 1


def erase(bit: int) -> int:
    if bit not in (0, 1):
        raise ValueError('binary state required')
    return 0


def landauer_floor_joule(temperature_kelvin: Decimal, erased_bits: int = 1) -> Decimal:
    """Conditional erasure lower bound, not measured actual switching energy."""
    if temperature_kelvin <= 0 or erased_bits < 0:
        raise ValueError('positive temperature and nonnegative erased bits')
    return K_B * temperature_kelvin * LN2 * erased_bits


def infoton_defined_mass_kg(temperature_kelvin: Decimal) -> Decimal:
    """Mass equivalent by definition E/c²; NOT a detected particle mass."""
    return landauer_floor_joule(temperature_kelvin) / (C*C)


def membrane_cyclic_frequency_hz(voltage: Decimal) -> Decimal:
    """Energy-equivalent frequency e*abs(V)/h; not an observed oscillator."""
    return E_CHARGE * abs(voltage) / H


def fermi_occupation_at_landauer() -> Decimal:
    """Mathematical occupation at E - mu = k_B T ln 2; not electric charge."""
    return Decimal(1) / (LN2.exp() + 1)


def audit() -> dict:
    reported_ratio = Fraction(SOURCE['ecc_verified_operations'], SOURCE['p30_ingress_only_operations'])
    operations_saved = Fraction(584 - 3, 584)
    normalized_rack = Fraction(SOURCE['conventional_rack_kw'] * SOURCE['p30_ingress_only_operations'], SOURCE['ecc_verified_operations'])
    units = coprime_residues(30)
    rng = random.Random(20261115)
    corpora = {
        'empty': b'',
        'zeroes_256': bytes(256),
        'alternating_256': bytes([0, 255]) * 128,
        'every_byte': bytes(range(256)),
        'seeded_random_256': rng.randbytes(256),
        'utf8_phrase': 'finite receipts; no thermodynamic inference'.encode(),
    }
    cases = []
    for name, payload in corpora.items():
        enc30 = radix_encode(payload, 30)
        enc8 = radix_encode(payload, 8)
        assert radix_decode(enc30, 30) == payload
        assert radix_decode(enc8, 8) == payload
        cases.append({
            'name': name,
            'input_bytes': len(payload),
            'zlib_bytes': len(zlib.compress(payload, level=9)),
            'base30_digits': len(enc30[1]),
            'base8_digits': len(enc8[1]),
            'base30_digits_fixed_width_bits_lower_bound': theoretical_fixed_digits_bits(30, len(enc30[1])),
            'base8_digits_fixed_width_bits_lower_bound': theoretical_fixed_digits_bits(8, len(enc8[1])),
            'verified_roundtrip': True,
        })
    return {
        'description': 'Audited arithmetic and counterexamples, NOT original P30 reproduction',
        'source_reported': SOURCE,
        'phi_30_units': list(units),
        'phi_30': len(units),
        '30_is_prime': False,
        'digits_for_256_classical_states_base30': min_digits_for_alphabet(256, 30),
        'digits_for_256_classical_states_coprime_positions': min_digits_for_alphabet(256, len(units)),
        'proposed_ratio_exact': f'{reported_ratio.numerator}/{reported_ratio.denominator}',
        'proposed_ratio_approx': round(float(reported_ratio), 6),
        'if_operation_counts_are_identical_3_vs_584_fraction_saved': f'{operations_saved.numerator}/{operations_saved.denominator}',
        'mode_roundtrip_p30_vs_utf8_extra_bytes': SOURCE['p30_packed_roundtrip_bytes'] - SOURCE['utf8_bytes'],
        'huffman_payload_vs_p30_direct_packed_extra_bytes': SOURCE['p30_direct_packed_write_only_bytes'] - SOURCE['huffman_payload_only_bytes'],
        'rack_kw_if_unverified_linear_scaling_is_assumed': round(float(normalized_rack), 6),
        'legal_position_substitution_undetected_by_membership_test': {'before': 1, 'after': 7, 'membership_before': is_valid_coprime_position(1), 'membership_after': is_valid_coprime_position(7)},
        'toggle_is_invertible': all(toggle(toggle(x)) == x for x in (0, 1)),
        'erase_is_not_injective': erase(0) == erase(1),
        'landauer_erasure_floor_300K_joule': str(landauer_floor_joule(Decimal(300))),
        'mass_equivalent_300K_kg': str(infoton_defined_mass_kg(Decimal(300))),
        'fermi_occupation_at_landauer_chemical_potential_zero': str(fermi_occupation_at_landauer()),
        'membrane_frequency_at_150mV_hz': str(membrane_cyclic_frequency_hz(Decimal('0.15'))),
        'synthetic_corpora': cases,
        'claims_not_proved': [
            'Original P30 codec semantics or robust integrity under arbitrary faults',
            'Equivalent ECC strength and total count of decoding, reads, storage, and writes',
            'Measured P30 latency, power or water savings on matched hardware',
            'Existence of a new information particle from mass-energy accounting',
            'Electric charge derived from occupation statistics',
            'Mitochondrial physical oscillation measured at energy-equivalent frequency',
            'Nuclear reactor fleet-wide fixed two-second blind window',
            'Legal prohibition on alternative-than-IBM data architectures',
        ],
    }


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--json', action='store_true')
    args = p.parse_args()
    report = audit()
    if args.json:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps({k: v for k, v in report.items() if k != 'synthetic_corpora'}, indent=2))


if __name__ == '__main__':
    main()
