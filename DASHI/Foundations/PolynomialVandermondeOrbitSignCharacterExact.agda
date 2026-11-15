module DASHI.Foundations.PolynomialVandermondeOrbitSignCharacterExact where

------------------------------------------------------------------------
-- COMMON ABSTRACT SIGN REPRESENTATION, WITHOUT A FALSE SAME-OBJECT
-- CLAIM. The video cubic Vandermonde V belongs to a rational-root
-- representation of S3; the four reflection-odd 27-map orbit-field
-- coordinates belong to a DIFFERENT F3 representation of S3.
-- Both actions factor through the ORIGINAL sign S3->C2.
--
-- Reuses exact previous owners:
-- PolynomialVandermondeOrbitParityIntertwinerExact (36+162 tables)
-- PolynomialC3S3ReflectionParityFourierExact (7+4 dual chart)
-- TernaryPermutationCyclicSubgroupsExact (additive F3, C2)
-- Classical sign character and Fourier of C2 are prior art.
-- SOURCE-WRITTEN, Agda kernel verification PENDING.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Cognition.PhaseEnrichedTrit as Phase
import DASHI.Foundations.StageSymmetryCarrierTowerExact as Stage
import DASHI.Foundations.TernaryEndomorphismConjugacyExact as Shape
import DASHI.Foundations.TernaryPermutationCyclicSubgroupsExact as Cyclic
import DASHI.Foundations.PolynomialC3S3TwentySevenOrbitQuotientExact as Q
import DASHI.Foundations.PolynomialC3S3ReflectionParityFourierExact as Fourier
import DASHI.Foundations.PolynomialVandermondeOrbitParityIntertwinerExact as Parity

-- Pullback of the ACTUAL full S3 action, factored through parity
-- on 11 C3-conjugacy classes.
pullbackSignField :
  Shape.TriPermutation → Q.Field11 → Q.Field11
pullbackSignField p f o =
  f (Parity.fullS3ActionOnEleven p o)

evenSevenIntertwines :
  (p : Shape.TriPermutation) (f : Q.Field11)
  (s : Shape.ShapeOrbit7) →
  Fourier.encodeEven (pullbackSignField p f) s ≡
  Fourier.encodeEven f s
evenSevenIntertwines Shape.permIdentity f s = refl
evenSevenIntertwines Shape.permRotate f s = refl
evenSevenIntertwines Shape.permRotate2 f s = refl
evenSevenIntertwines Shape.permSwapLowMid f s = Fourier.reflectEvenIsFixed f s
evenSevenIntertwines Shape.permSwapLowHigh f s = Fourier.reflectEvenIsFixed f s
evenSevenIntertwines Shape.permSwapMidHigh f s = Fourier.reflectEvenIsFixed f s

data OddSlot4 : Set where
  cycleSlot oneFixedSlot twoFixedSlot twoCycleSlot : OddSlot4

oddAt : Fourier.Odd4 → OddSlot4 → Phase.Phase3
oddAt o cycleSlot = Fourier.cycleOdd o
oddAt o oneFixedSlot = Fourier.rank2OneFixedOdd o
oddAt o twoFixedSlot = Fourier.rank2TwoFixedOdd o
oddAt o twoCycleSlot = Fourier.rank2TwoCycleOdd o

signPhase : Stage.C2 → Phase.Phase3 → Phase.Phase3
signPhase Stage.direct value = value
signPhase Stage.inverse value = Cyclic.c3Inverse value

oddSignIntertwines :
  (p : Shape.TriPermutation) (f : Q.Field11) (slot : OddSlot4) →
  oddAt (Fourier.encodeOdd (pullbackSignField p f)) slot ≡
  signPhase (Parity.permutationParity p)
    (oddAt (Fourier.encodeOdd f) slot)
oddSignIntertwines Shape.permIdentity f cycleSlot = refl
oddSignIntertwines Shape.permIdentity f oneFixedSlot = refl
oddSignIntertwines Shape.permIdentity f twoFixedSlot = refl
oddSignIntertwines Shape.permIdentity f twoCycleSlot = refl
oddSignIntertwines Shape.permRotate f cycleSlot = refl
oddSignIntertwines Shape.permRotate f oneFixedSlot = refl
oddSignIntertwines Shape.permRotate f twoFixedSlot = refl
oddSignIntertwines Shape.permRotate f twoCycleSlot = refl
oddSignIntertwines Shape.permRotate2 f cycleSlot = refl
oddSignIntertwines Shape.permRotate2 f oneFixedSlot = refl
oddSignIntertwines Shape.permRotate2 f twoFixedSlot = refl
oddSignIntertwines Shape.permRotate2 f twoCycleSlot = refl
oddSignIntertwines Shape.permSwapLowMid f cycleSlot = Fourier.reflectOddCycleIsNegative f
oddSignIntertwines Shape.permSwapLowMid f oneFixedSlot = Fourier.reflectOddOneFixedIsNegative f
oddSignIntertwines Shape.permSwapLowMid f twoFixedSlot = Fourier.reflectOddTwoFixedIsNegative f
oddSignIntertwines Shape.permSwapLowMid f twoCycleSlot = Fourier.reflectOddTwoCycleIsNegative f
oddSignIntertwines Shape.permSwapLowHigh f cycleSlot = Fourier.reflectOddCycleIsNegative f
oddSignIntertwines Shape.permSwapLowHigh f oneFixedSlot = Fourier.reflectOddOneFixedIsNegative f
oddSignIntertwines Shape.permSwapLowHigh f twoFixedSlot = Fourier.reflectOddTwoFixedIsNegative f
oddSignIntertwines Shape.permSwapLowHigh f twoCycleSlot = Fourier.reflectOddTwoCycleIsNegative f
oddSignIntertwines Shape.permSwapMidHigh f cycleSlot = Fourier.reflectOddCycleIsNegative f
oddSignIntertwines Shape.permSwapMidHigh f oneFixedSlot = Fourier.reflectOddOneFixedIsNegative f
oddSignIntertwines Shape.permSwapMidHigh f twoFixedSlot = Fourier.reflectOddTwoFixedIsNegative f
oddSignIntertwines Shape.permSwapMidHigh f twoCycleSlot = Fourier.reflectOddTwoCycleIsNegative f

-- Two independently typed intertwiners have the SAME p : S3.
-- In the roots lane, rational Vandermonde transforms by +/-1.
-- In the orbit-field lane, all four odd F3 coordinates transform
-- by +/-1 and seven even coordinates are fixed.
-- This is the precise cross-pollination, NOT the claim that the
-- four F3 coordinates equal polynomial discriminants or roots.
