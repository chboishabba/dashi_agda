"""Exact balanced/369 three-Fourier-mode codec and NS quadratic aliasing audit.

This is finite-mode arithmetic. It does not type-check Agda or establish
physical Ma-lattice, R2P2, nonlinear Navier–Stokes or Clay statements.
"""
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from r2p2_three_mode_codec_ns_aliasing_diagnostic import (  # noqa: E402
    MODES, CODEC, DECODE, BINARY_IN_TERNARY,
    centered_mod, exact_quadratic_product, sampled_quadratic_product,
    kept_modes, audit,
)

AGDA = ROOT / "DASHI/Physics/Closure/R2P2ThreeModeBinaryTernaryNSAliasingCutExact.agda"
ARCH = ROOT / "DASHI/Physics/Closure/R2P2369AtomicQuantumDiamondArchitectureExact.agda"
ROOTS = (
    ROOT / "DASHI/EverythingTOESymmetryResolved369.agda",
    ROOT / "DASHI/Unifier.agda",
    ROOT / "DASHI/Unified/Everything.agda",
)


class ThreeModeNSCodecTests(unittest.TestCase):
    def test_lossless_trit_as_binary_and_strict_binary_in_ternary(self):
        self.assertEqual(MODES, (-1, 0, 1))
        self.assertTrue(all(DECODE[CODEC[m]] == m for m in MODES))
        self.assertIsNone(DECODE[(1, 1)])
        self.assertEqual(BINARY_IN_TERNARY, {False: -1, True: 1})
        self.assertNotIn(0, BINARY_IN_TERNARY.values())

    def test_out_of_window_plus_two_aliases_to_minus_one(self):
        self.assertEqual(centered_mod(2, 3), -1)
        self.assertEqual(centered_mod(-2, 3), 1)
        self.assertEqual(centered_mod(2, 5), 2)
        exact, aliased = kept_modes((0, 0, 1), 3)
        self.assertEqual(exact, (0, 0, 0))
        self.assertEqual(aliased, (1, 0, 0))
        self.assertEqual(exact_quadratic_product((0, 0, 1))[2], 1)

    def test_all_27_balanced_input_profiles(self):
        summary = audit()
        self.assertEqual(summary["balanced_input_profiles"], 27)
        self.assertEqual(summary["three_point_profiles_with_alias_in_kept_modes"], 24)
        self.assertEqual(summary["five_point_profiles_with_alias_in_kept_modes"], 0)
        self.assertFalse(summary["ns_clay_or_qg_proved"])
        self.assertFalse(summary["r2p2_optical_clock_measured"])

    def test_codec_roundtrip_does_not_mean_alias_free(self):
        inputs = (-1, 0, 1)
        encoded = tuple(CODEC[m] for m in inputs)
        decoded = tuple(DECODE[bits] for bits in encoded)
        self.assertEqual(decoded, inputs)
        self.assertNotEqual(kept_modes((0, 0, 1), 3)[0], kept_modes((0, 0, 1), 3)[1])

    def test_original_agda_owners_and_nonpromotion(self):
        content = AGDA.read_text(encoding="utf-8")
        for name in (
            "VerifiedFiniteTritCoder",
            "BinaryBalancedTernarySubcarrierExact",
            "BalancedTernaryQutritBasisBridgeExact",
            "NSIntegerFourierLattice",
            "NSCross369OrientationBridgeExact",
            "NSTriadKN369HighHighGramBridgeReceipt",
            "SparseTwistLESBridge",
            "IntersectionalNonFactorability",
            "positivePositiveLeavesThreeModeWindow",
            "positivePositiveAliasesToNegative",
            "wideModeAliasCollision",
            "foldedThreePointModeCannotRecoverExactFourierIndex",
            "rechartingThreePointModeCannotFixAliasing",
            "nsExactPlusPlusIsPlusTwoX",
            "maThreeModeSourceSidebandsAreOutOfWindow",
            "threeModeCodecIsNotAnNSProof",
        ):
            with self.subTest(name=name):
                self.assertIn(name, content)
        for escape in ("postulate\n", "{!!}", "{-# TERMINATING #-}", "{-# NO_POSITIVITY_CHECK #-}"):
            self.assertNotIn(escape, content)

    def test_toe_roots_and_experiment_architecture(self):
        import_name = "DASHI.Physics.Closure.R2P2ThreeModeBinaryTernaryNSAliasingCutExact"
        architecture = ARCH.read_text(encoding="utf-8")
        self.assertIn(import_name, architecture)
        self.assertIn("fullArchitectureThreePointModeDoesNotRecoverIntegerLabel", architecture)
        for path in ROOTS:
            with self.subTest(path=str(path)):
                src = path.read_text(encoding="utf-8")
                self.assertIn(import_name, src)
                self.assertIn("ThreeModeBinaryTernaryCodecRoundTrip", src)
                self.assertIn("ThreeModeFourierQuadraticAlias", src)
                self.assertIn("ThreeModeBinaryTernaryDoesNotProveNS", src)


if __name__ == "__main__":
    unittest.main()
