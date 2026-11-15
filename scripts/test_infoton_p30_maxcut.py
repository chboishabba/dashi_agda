#!/usr/bin/env python3
"""Deterministic exact checks, executable with python -m unittest."""
import math
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
import random
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import infoton_p30_maxcut as m


class P30FiniteAudit(unittest.TestCase):
    def test_nonprime_phi_30(self):
        self.assertEqual(math.gcd(5, 30), 5)
        self.assertEqual(m.coprime_residues(30), (1, 7, 11, 13, 17, 19, 23, 29))

    def test_fixed_capacity(self):
        self.assertEqual(m.min_digits_for_alphabet(256, 30), 2)
        self.assertEqual(m.min_digits_for_alphabet(256, 8), 3)
        self.assertEqual(m.theoretical_fixed_digits_bits(8, 3), 9)
        self.assertEqual(m.theoretical_fixed_digits_bits(30, 2), 10)

    def test_uniform_byte_roundtrip(self):
        for b in range(256):
            payload = bytes([b])
            for radix in (2, 3, 8, 16, 30, 256):
                self.assertEqual(m.radix_decode(m.radix_encode(payload, radix), radix), payload)

    def test_zero_byte_length_and_random_roundtrip(self):
        rng = random.Random(20261115)
        for length in (0, 1, 2, 7, 16, 163, 256):
            for payload in (bytes(length), rng.randbytes(length)):
                for radix in (3, 8, 30):
                    self.assertEqual(m.radix_decode(m.radix_encode(payload, radix), radix), payload)

    def test_malformed_codes_rejected(self):
        with self.assertRaises(ValueError):
            m.radix_decode((1, (30,)), 30)
        with self.assertRaises(ValueError):
            m.radix_decode((1, (8, 16)), 30)

    def test_membership_check_cannot_detect_legal_substitution(self):
        self.assertTrue(m.is_valid_coprime_position(1))
        self.assertTrue(m.is_valid_coprime_position(7))
        self.assertNotEqual(1, 7)
        self.assertFalse(m.is_valid_coprime_position(6))

    def test_reversible_flip_not_erasure(self):
        for x in (0, 1):
            self.assertEqual(m.toggle(m.toggle(x)), x)
        self.assertEqual(m.erase(0), m.erase(1))

    def test_original_reported_storage_and_operation_arithmetic(self):
        s = m.SOURCE
        self.assertEqual(s['p30_packed_roundtrip_bytes'] - s['utf8_bytes'], 8)
        self.assertEqual(s['p30_direct_packed_write_only_bytes'] - s['huffman_payload_only_bytes'], 13)
        self.assertGreater(Fraction(12264, 163), 75)
        self.assertLess(Fraction(12264, 163), 76)
        self.assertEqual(75 * 163 + 39, 12264)
        self.assertEqual(Fraction(584 - 3, 584), Fraction(581, 584))

    def test_fermi_algebraic_identity(self):
        x = m.fermi_occupation_at_landauer()
        self.assertLess(abs(x - Decimal(1) / 3), Decimal('1e-45'))

    def test_landauer_mass_and_frequency_are_only_algebra(self):
        t = Decimal(300)
        self.assertEqual(m.infoton_defined_mass_kg(t) * m.C * m.C, m.landauer_floor_joule(t))
        self.assertTrue(Decimal('3e-38') < m.infoton_defined_mass_kg(t) < Decimal('4e-38'))
        self.assertTrue(Decimal('3e13') < m.membrane_cyclic_frequency_hz(Decimal('0.15')) < Decimal('4e13'))

    def test_receipt_has_physical_claim_boundaries(self):
        r = m.audit()
        self.assertEqual(r['phi_30'], 8)
        self.assertEqual(len(r['synthetic_corpora']), 6)
        self.assertGreaterEqual(len(r['claims_not_proved']), 8)


if __name__ == '__main__':
    unittest.main()
