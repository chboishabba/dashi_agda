"""Source-defined 13-in-27, 5-in-9 orbit Fourier symmetry and no-go."""
from pathlib import Path
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from r2p2_13in27_5in9_hermitian_symmetry import (  # noqa: E402
    CUBE27, PLANE9, PAIRS729,
    neg, representative, conjugate, sample_hermitian,
    pack_hermitian, unpack_hermitian, convolution, plane_convolution,
    folded_hermitian_output, audit,
)

SOURCE=ROOT/"DASHI/Physics/Closure/R2P227729AntipodalThirteenFiveOrbitFourierCutExact.agda"
CODEC=ROOT/"DASHI/Physics/Closure/R2P227729HermitianThirteenPairFourierCodecExact.agda"
TRANSPORT=ROOT/"DASHI/Physics/Closure/R2P227729HermitianConvolutionTransportExact.agda"
PLANE_TRANSPORT=ROOT/"DASHI/Physics/Closure/R2P281PlaneHermitianFiveOrbitConvolutionExact.agda"
NYQUIST=ROOT/"DASHI/Physics/Closure/R2P2C4C5NyquistAntipodalFixedPointExact.agda"
ROOTS=[
 ROOT/"DASHI/EverythingTOESymmetryResolved369.agda",
 ROOT/"DASHI/Unifier.agda",
 ROOT/"DASHI/Unified/Everything.agda",
]

class AntipodalFourierTests(unittest.TestCase):
    def test_source_thirteen_and_five_counts(self):
        a=audit()["source_orbit_counts"]
        self.assertEqual((a["cube_nonneutral_pairs"],a["cube_classes"]),(13,14))
        self.assertEqual((a["plane_nonneutral_pairs"],a["plane_classes"]),(4,5))
        self.assertEqual((a["pair_nonneutral_antipodal_pairs"],a["pair_orbit_classes"]),(364,365))
        self.assertEqual(a["wide_product_antipodal_classes"],63)

    def test_real_field_packing_unpacks_every_coefficient(self):
        for modes in (CUBE27,PLANE9):
            values=sample_hermitian(modes)
            packed=pack_hermitian(values,modes)
            self.assertEqual(len(packed),(len(modes)+1)//2)
            self.assertEqual(unpack_hermitian(packed,modes),values)
            self.assertTrue(all(values[neg(k)]==conjugate(values[k]) for k in modes))

    def test_quadratic_convolution_conjugation_closure(self):
        left=sample_hermitian(CUBE27)
        right=sample_hermitian(CUBE27,variant=1)
        self.assertNotEqual(left,right)
        result=convolution(left,right)
        self.assertEqual(len(result),125)
        self.assertTrue(all(result[neg(k)]==conjugate(v) for k,v in result.items()))
        self.assertEqual(
            result,
            convolution(
                unpack_hermitian(pack_hermitian(left,CUBE27),CUBE27),
                unpack_hermitian(pack_hermitian(right,CUBE27),CUBE27)))

    def test_five_in_nine_quadratic_plane_81_pairs(self):
        left=sample_hermitian(PLANE9)
        right=sample_hermitian(PLANE9,variant=2)
        self.assertNotEqual(left,right)
        output=plane_convolution(left,right)
        self.assertEqual(len(output),25)
        self.assertTrue(all(output[neg(k)]==conjugate(v) for k,v in output.items()))
        self.assertEqual(
            output,plane_convolution(
                unpack_hermitian(pack_hermitian(left,PLANE9),PLANE9),
                unpack_hermitian(pack_hermitian(right,PLANE9),PLANE9)))

    def test_even_grid_eight_real_nyquist_corners(self):
        a=sample_hermitian(CUBE27)
        b=sample_hermitian(CUBE27,variant=1)
        output=convolution(a,b)
        four=folded_hermitian_output(output,4)
        five=folded_hermitian_output(output,5)
        self.assertEqual(
            (four["self_antipodal_frequency_classes"],
             four["nonfixed_conjugate_pairs"],
             four["total_inversion_orbit_classes"]), (8,28,36))
        self.assertEqual(
            (five["self_antipodal_frequency_classes"],
             five["nonfixed_conjugate_pairs"],
             five["total_inversion_orbit_classes"]), (1,62,63))
        self.assertTrue(four["real_coefficients_at_all_self_antipodal_outputs"])
        self.assertTrue(five["real_field_output_conjugate_symmetry"])

    def test_orbit_labels_drop_pair_sum_orientation(self):
        plus=(1,0,0); minus=(-1,0,0)
        self.assertEqual(representative(plus),representative(minus))
        self.assertNotEqual(
            tuple(a+b for a,b in zip(plus,plus)),
            tuple(a+b for a,b in zip(minus,plus)))
        self.assertFalse(audit()["operator_cut"]["pair_orbit_labels_determine_true_integer_sum"])

    def test_source_owner_provenance_and_no_escape(self):
        code=SOURCE.read_text(encoding="utf-8")
        codec=CODEC.read_text(encoding="utf-8")
        for token in (
            "BalancedTernaryAntipodalOrbitExact",
            "BalancedTernaryAntipodal369OrbitHierarchyExact",
            "TernaryNineAntipodalD4SeparationExact",
            "planeClassInclusionCommutes",
            "sourceThirteenNonzeroPairs",
            "sourceFiveNineOrbitCount",
            "noIntegerPairOutputFromOnlyOrbitLabels",
            "trueIntegerQuadraticPairSumNegationEquivariance",
            "orderedPairOutputCovariantUnderSimultaneousNegation",
        ): self.assertIn(token,code)
        for token in (
            "PackedHermitian27","PackedHermitian9",
            "representativeMatchesSelectedOrientation",
            "decodeAfterEncodeHermitian27",
            "decodeAfterEncodeHermitian9",
            "storedIndependentComplexPairs",
            "realScalarDegreesOfFreedom",
            "planeRealScalarDegreesOfFreedom",
            "C3CubeCyclotomicFourierExact",
        ): self.assertIn(token,codec)
        transport=TRANSPORT.read_text(encoding="utf-8")
        for token in ("compact13PairTransportPreservesAll125IntegerOutputs",
                      "compact13PairsPreserveFourGridRetainedQuadratic",
                      "compact13PairsPreserveFiveGridFullQuadratic",
                      "sumUsingCong"):
            self.assertIn(token,transport)
        plane_transport=PLANE_TRANSPORT.read_text(encoding="utf-8")
        for token in ("planePairCountEightyOne",
                      "fiveOrbitPlaneCodecPreservesAll25QuadraticOutputs",
                      "packedPlanePairTermMatchesSource"):
            self.assertIn(token,plane_transport)
        nyquist=NYQUIST.read_text(encoding="utf-8")
        for token in ("fourCubeHasEightFixedAntipodes",
                      "fourCubeHas28NonfixedAntipodalPairs",
                      "fourCubeOrbitClasses36",
                      "fourGridFlagIfAndOnlyIfActuallySelfNegativeForward",
                      "fourGridFlagIfAndOnlyIfActuallySelfNegativeBackward",
                      "fiveCubeHasOneFixedAntipode",
                      "fiveCubeHas62AntipodalPairs",
                      "fiveCubeOrbitClasses63",
                      "fiveGridFlagIfAndOnlyIfActuallySelfNegativeForward",
                      "fiveGridFlagIfAndOnlyIfActuallySelfNegativeBackward"):
            self.assertIn(token,nyquist)
        for src in (code,codec,transport,plane_transport,nyquist):
            for escape in ("{!!}","postulate\n","{-# TERMINATING #-}",
                           "{-# NO_POSITIVITY_CHECK #-}","allow-unsolved-metas"):
                self.assertNotIn(escape,src)

    def test_toe_roots_reference_original_orbit_owners(self):
        for root in ROOTS:
            with self.subTest(root=root):
                content=root.read_text(encoding="utf-8")
                self.assertIn("R2P227729AntipodalThirteenFiveOrbitFourierCutExact",content)
                self.assertIn("R2P227729HermitianThirteenPairFourierCodecExact",content)
                self.assertIn("R2P227729HermitianConvolutionTransportExact",content)
                self.assertIn("R2P281PlaneHermitianFiveOrbitConvolutionExact",content)
                self.assertIn("R2P2C4C5NyquistAntipodalFixedPointExact",content)
                self.assertIn("Hermitian",content)
                self.assertIn("Antipodal",content)

if __name__=="__main__":
    unittest.main()
