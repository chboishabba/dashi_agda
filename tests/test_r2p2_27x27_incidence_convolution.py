"""R2P2 finite Fourier 27:729 source-correctness regression.

The test is only Python exact integer execution and static Agda source checks.
No kernel replay, scientific NS solution or actual clock calibration.
"""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from r2p2_27x27_incidence_convolution_diagnostic import (  # noqa: E402
    CUBE27, PAIRS729, WIDE125, six_trits, pair_from_six_trits,
    integer_sum, inside_cube, grid5_index, recover_grid5,
    exact_convolution, index_recovered_five_convolution,
    aliased_three_convolution, audit,
)

OWNERS = [
    ROOT / "DASHI/Physics/Closure/R2P227729FourierObserverIncidenceExact.agda",
    ROOT / "DASHI/Physics/Closure/R2P227729PairSixTritFibreBidiExact.agda",
    ROOT / "DASHI/Physics/Closure/R2P227729FiniteQuadraticConvolutionExact.agda",
    ROOT / "DASHI/Physics/Closure/R2P227729ExistingC3FourierConvolutionReuseExact.agda",
]


class Finite729Tests(unittest.TestCase):
    def test_complete_unique_six_trit_ordered_pairs(self):
        self.assertEqual(len(CUBE27), 27)
        self.assertEqual(len(set(CUBE27)), 27)
        self.assertEqual(len(PAIRS729), 729)
        codes = [six_trits(pair) for pair in PAIRS729]
        self.assertEqual(len(set(codes)), 729)
        self.assertTrue(all(pair_from_six_trits(code) == pair
                            for code, pair in zip(codes, PAIRS729)))

    def test_actual_inside_outside_pair_classification(self):
        inside = sum(inside_cube(integer_sum(p, q)) for p, q in PAIRS729)
        self.assertEqual((inside, 729 - inside), (343, 386))

    def test_five_grid_covers_every_wide_mode_without_collisions(self):
        self.assertEqual(len(WIDE125), 125)
        self.assertEqual(len(set(map(grid5_index, WIDE125))), 125)
        self.assertTrue(all(recover_grid5(grid5_index(k)) == k for k in WIDE125))

    def test_multiple_arbitrary_natural_amplitudes(self):
        for fn in (
            lambda k, i: 0,
            lambda k, i: 1,
            lambda k, i: i % 5,
            lambda k, i: int(k == (1, 0, 0)),
            lambda k, i: (abs(k[0]) + 2*abs(k[1]) + 3*abs(k[2]))**2,
        ):
            amplitudes = {k: fn(k, i) for i, k in enumerate(CUBE27)}
            exact = exact_convolution(amplitudes)
            recovered = index_recovered_five_convolution(amplitudes)
            self.assertEqual(
                [exact[k] for k in WIDE125],
                [recovered[k] for k in WIDE125],
            )

    def test_wide_mode_collision_does_not_recover_integer_frequency(self):
        high = (2, 0, 0)
        low = (-1, 0, 0)
        self.assertNotEqual(high, low)
        folded = lambda k: tuple((v + 1) % 3 - 1 for v in k)
        self.assertEqual(folded(high), folded(low))
        self.assertEqual(folded(high), (-1, 0, 0))

    def test_three_grid_folds_false_retained_frequency(self):
        single = {k: int(k == (1, 0, 0)) for k in CUBE27}
        exact, folded = exact_convolution(single), aliased_three_convolution(single)
        self.assertEqual(exact[(2, 0, 0)], 1)
        self.assertEqual(exact[(-1, 0, 0)], 0)
        self.assertEqual(folded[(-1, 0, 0)], 1)

    def test_summary_keeps_distinct_proof_and_physics_status(self):
        r = audit()
        self.assertEqual(r["inside_integer_sum_window"], 343)
        self.assertEqual(r["outside_integer_sum_window"], 386)
        self.assertFalse(r["claimed_full_DFT_or_NS_solution"])
        self.assertFalse(r["claimed_GF729_or_Monster_action"])
        self.assertFalse(r["claimed_R2P2_physical_measurement"])

    def test_agda_new_owner_contracts(self):
        source = [path.read_text(encoding="utf-8") for path in OWNERS]
        self.assertIn("signAndResidueDisagreeOnPositiveTwo", source[0])
        self.assertIn("cube27HasExactly27Entries", source[0])
        self.assertIn("pair729HasExactly729Entries", source[0])
        self.assertIn("exact343InWindowPairs", source[0])
        self.assertIn("exact386OutOfWindowPairs", source[0])
        self.assertIn("modeVoxelRoundTrip", source[0])
        self.assertIn("cube27RanksAreExactlyZeroThrough26", source[0])
        self.assertIn("orderedPairRanksAreExactlyZeroThrough728", source[0])
        self.assertIn("pathXAxisWraparoundIsImpossible", source[0])
        self.assertIn("periodicXAxisWraparoundExists", source[0])
        self.assertIn("voxelModeRoundTrip", source[0])
        self.assertIn("sixTritsAfterOrderedPairRoundTrip", source[1])
        self.assertIn("orderedPairAfterSixTritRoundTrip", source[1])
        self.assertIn("pairAmplitudeAfterTransport", source[1])
        self.assertIn("sixTritAmplitudeAfterTransport", source[1])
        self.assertIn("all729PairsFiveIndexRecoveryIsExact", source[2])
        self.assertIn("retainedFiveIndexConvolutionExact", source[2])
        self.assertIn("threeAxisCyclicIndexCollision", source[2])
        self.assertIn("noDecoderOfActualWideModeFromCyclic27", source[2])
        self.assertIn("cyclic27RechartCannotUndoWideFrequencyLoss", source[2])
        for key in ("C3CubeCyclotomicFourierExact", "C3CubeCyclotomicParsevalExact",
                    "C3CubeDirectGroupConvolutionExact",
                    "signedModeToCyclicResidueConvention",
                    "packAfterUnpack", "unpackAfterPack",
                    "existingPeriodic27FourierRoundTrip",
                    "periodic27DirectEqualsSpectralAtEveryMode",
                    "existingCyclic27Parseval"):
            self.assertIn(key, source[3])
        for path, text in zip(OWNERS, source):
            with self.subTest(path=str(path)):
                for escape in ("postulate\n", "{!!}", "{-# TERMINATING #-}",
                               "{-# NO_POSITIVITY_CHECK #-}", "--allow-unsolved-metas"):
                    self.assertNotIn(escape, text)


if __name__ == "__main__":
    unittest.main()
