"""Source-defined 13-in-27, 5-in-9 orbit Fourier symmetry and no-go."""
from pathlib import Path
import sys
import unittest

ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/"scripts"))
from r2p2_13in27_5in9_hermitian_symmetry import (  # noqa: E402
    CUBE27, PLANE9, PAIRS729,
    neg, representative, conjugate, sample_hermitian,
    pack_hermitian, unpack_hermitian, convolution, audit,
)

SOURCE=ROOT/"DASHI/Physics/Closure/R2P227729AntipodalThirteenFiveOrbitFourierCutExact.agda"
CODEC=ROOT/"DASHI/Physics/Closure/R2P227729HermitianThirteenPairFourierCodecExact.agda"
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
        for src in (code,codec):
            for escape in ("{!!}","postulate\n","{-# TERMINATING #-}",
                           "{-# NO_POSITIVITY_CHECK #-}","allow-unsolved-metas"):
                self.assertNotIn(escape,src)

    def test_toe_roots_reference_original_orbit_owners(self):
        for root in ROOTS:
            with self.subTest(root=root):
                content=root.read_text(encoding="utf-8")
                self.assertIn("R2P227729AntipodalThirteenFiveOrbitFourierCutExact",content)
                self.assertIn("R2P227729HermitianThirteenPairFourierCodecExact",content)
                self.assertIn("Hermitian",content)
                self.assertIn("Antipodal",content)

if __name__=="__main__":
    unittest.main()
