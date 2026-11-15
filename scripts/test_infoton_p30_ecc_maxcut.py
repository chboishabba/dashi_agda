#!/usr/bin/env python3
"""Reference fault audit; standard-library only."""
from pathlib import Path
from fractions import Fraction
import random
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import infoton_p30_ecc_maxcut as a


class InfotonP30ECCMaxCut(unittest.TestCase):
    def test_column_count(self):
        self.assertEqual(len(a.COLUMNS), 72)
        self.assertEqual(len(set(a.COLUMNS)), 72)
        self.assertTrue(all(c.bit_count() % 2 == 1 for c in a.COLUMNS))

    def test_zero_and_maxword(self):
        for data in (0, a.MASK64):
            self.assertEqual(a.syndrome(a.encode72(data)), 0)
            self.assertEqual(a.decode72(a.encode72(data)).data, data)

    def test_72_single_faults(self):
        for data in (0, a.MASK64, 0x0123456789abcdef):
            codeword = a.encode72(data)
            for i in range(72):
                result = a.decode72(codeword ^ (1 << i))
                self.assertEqual(result.data, data)
                self.assertEqual(result.status, "single_corrected")
                self.assertEqual(result.position, i)

    def test_2556_double_faults(self):
        codeword = a.encode72(0x0123456789abcdef)
        for i in range(72):
            for j in range(i + 1, 72):
                self.assertEqual(
                    a.decode72(codeword ^ (1 << i) ^ (1 << j)).status,
                    "detected_uncorrectable")

    def test_seeded_words(self):
        r = random.Random(20261115)
        for _ in range(200):
            d = r.getrandbits(64)
            self.assertEqual(a.decode72(a.encode72(d)).data, d)

    def test_all_bytes_surrogate_roundtrip(self):
        for b in range(256):
            self.assertEqual(a.decode_unit_surrogate(a.encode_unit_surrogate(b)), b)

    def test_valid_unit_corruption_not_protected(self):
        r = a.reference_receipt()
        self.assertEqual(r["surrogate_undetected"], 4352)
        self.assertEqual(r["surrogate_detected"], 1024)
        self.assertEqual(r["surrogate_undetected_fraction"], "17/21")
        self.assertFalse(r["original_P30_ECC_equivalence_proven"])

    def test_rack_fixed_floor(self):
        self.assertAlmostEqual(float(a.rack_projection(Fraction(0))), 130*163/12264)
        self.assertGreater(float(a.rack_projection(Fraction(25,100))), 30)
        self.assertEqual(a.rack_projection(Fraction(1)), 130)

    def test_out_of_range_codewords(self):
        for c in (-1, 1 << 72):
            with self.assertRaises(ValueError):
                a.syndrome(c)

    def test_composite_30(self):
        self.assertEqual(len(a.UNITS), 8)
        self.assertEqual(5 * 6, 30)

    def test_reference_fault_count(self):
        r = a.reference_receipt()
        self.assertEqual(r["reference_single_bit_corrected"], 72)
        self.assertEqual(r["reference_double_bit_detected"], 2556)

    def test_no_energy_measurement_promoted(self):
        self.assertFalse(a.reference_receipt()["hardware_energy_reduction_measured"])


if __name__ == "__main__":
    unittest.main()
