module DASHI.Moonshine.OggSSPP2InertiaMassVersusDefectSumNoGoExact where

------------------------------------------------------------------------
-- p=2 INERTIA: THE VALUATION OF A MASS IS NOT THE SUM OF DEFECTS
--
-- CLASSICAL INPUT (reused, not reattributed):
--   binary tetrahedral conjugacy-class sizes:
--        1,1,6,4,4,4,4
--   centralizer orders:
--        24,24,4,6,6,6,6.
--
-- The full inertia groupoid mass is sum_[g] 1/|C(g)| = 1.
-- Choosing ONE representative from each loop-reversal orbit gives the
-- five-term sum 1/24+1/24+1/4+1/6+1/6 = 2/3, with v2=1.
-- By contrast summing the five independent centralizer 2-defects gives 10.
--
-- IMPORTANT: the five-term sum is a REPRESENTATIVE-SAMPLED rational weight,
-- not automatically the mass of the loop-reversal quotient stack.  Quotient
-- automorphisms need to be constructed before assigning stacky mass.
--
-- DASHI THEOREM: v2(sum of these five rational weights) != sum v2(denoms).
-- Neither expression is a Carnahan/Urano finite-DVR length or a correction
-- to the Monster exponent without a further source-native theorem.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Moonshine.OggSSPP2BinaryTetrahedralInertiaFiveOrbitExact as Inertia
import DASHI.Moonshine.OggSSPP2InertiaCentralizerValuationExact as Centralizer
import DASHI.Moonshine.OggSSPP2InertiaConjugacyClassDefectExact as Defect
import DASHI.Moonshine.OggSSP2BSourceIndexedDVRValuationIdentificationExact as TwoB
import DASHI.Moonshine.OggSSPMonstrousExponentSourceAttributionExact as Attribution

------------------------------------------------------------------------
-- 1. Write the inverse centralizer weights with common denominator 24.
--    For each class, |class| = 24 / |C(g)|.
------------------------------------------------------------------------

numerator24 :
  Inertia.BinaryTetrahedralConjugacyClass -> Nat
numerator24 = Centralizer.classSize

fullInertiaNumerator24 : Nat
fullInertiaNumerator24 =
  numerator24 Inertia.identityClass
  + numerator24 Inertia.centralMinusOneClass
  + numerator24 Inertia.orderFourClass
  + numerator24 Inertia.orderThreePositiveClass
  + numerator24 Inertia.orderThreeNegativeClass
  + numerator24 Inertia.orderSixPositiveClass
  + numerator24 Inertia.orderSixNegativeClass

fullInertiaNumeratorIsTwentyFour :
  fullInertiaNumerator24 ≡ 24
fullInertiaNumeratorIsTwentyFour = refl

-- Seven-class inertia mass is 24/24=1.  This is the usual groupoid mass.
fullInertiaMassEqualsOneByCommonDenominator :
  fullInertiaNumerator24 ≡ 24 * 1
fullInertiaMassEqualsOneByCommonDenominator = refl

------------------------------------------------------------------------
-- 2. Five representative-sampled sectors, NOT a quotient-stack mass.
------------------------------------------------------------------------

sampledFiveNumerator24 : Nat
sampledFiveNumerator24 =
  numerator24
    (Centralizer.representativeClass Inertia.identityInertiaOrbit)
  + numerator24
    (Centralizer.representativeClass Inertia.centralMinusOneInertiaOrbit)
  + numerator24
    (Centralizer.representativeClass Inertia.orderFourInertiaOrbit)
  + numerator24
    (Centralizer.representativeClass Inertia.orderThreePairInertiaOrbit)
  + numerator24
    (Centralizer.representativeClass Inertia.orderSixPairInertiaOrbit)

sampledFiveNumeratorIsSixteen :
  sampledFiveNumerator24 ≡ 16
sampledFiveNumeratorIsSixteen = refl

-- Cross multiplication of 16/24 = 2/3.
sampledWeightReducesToTwoThirds :
  sampledFiveNumerator24 * 3 ≡ 24 * 2
sampledWeightReducesToTwoThirds = refl

-- Reduced numerator 2 is divisible by exactly one power of 2;
-- reduced denominator 3 is odd.  The rational sampled mass has v2=1.
sampledWeightReducedNumerator : Nat
sampledWeightReducedNumerator = 2

sampledWeightReducedDenominator : Nat
sampledWeightReducedDenominator = 3

sampledWeightTwoAdicValuation : Nat
sampledWeightTwoAdicValuation = 1

reducedNumeratorFactorization :
  sampledWeightReducedNumerator ≡ 2 * 1
reducedNumeratorFactorization = refl

reducedDenominatorOdd :
  sampledWeightReducedDenominator ≡ 2 * 1 + 1
reducedDenominatorOdd = refl

------------------------------------------------------------------------
-- 3. The DIFFERENT observable: sum of five class defects.
------------------------------------------------------------------------

fiveDefectSum : Nat
fiveDefectSum =
  Defect.conjugacyClassTwoDefect Inertia.identityInertiaOrbit
  + Defect.conjugacyClassTwoDefect Inertia.centralMinusOneInertiaOrbit
  + Defect.conjugacyClassTwoDefect Inertia.orderFourInertiaOrbit
  + Defect.conjugacyClassTwoDefect Inertia.orderThreePairInertiaOrbit
  + Defect.conjugacyClassTwoDefect Inertia.orderSixPairInertiaOrbit

fiveDefectSumIsTen :
  fiveDefectSum ≡ 10
fiveDefectSumIsTen = refl

sampledMassValuationIsNotFiveDefectSum :
  sampledWeightTwoAdicValuation ≡ fiveDefectSum -> ⊥
sampledMassValuationIsNotFiveDefectSum ()

fullInertiaMassValuation : Nat
fullInertiaMassValuation = 0

fullMassValuationIsNotFiveDefectSum :
  fullInertiaMassValuation ≡ fiveDefectSum -> ⊥
fullMassValuationIsNotFiveDefectSum ()

------------------------------------------------------------------------
-- 3b. Connect to the pre-existing 2B source slots, WITHOUT asserting
--     that any actual localized integral module has this composition length.
------------------------------------------------------------------------

fiveSourceSlotGeometricDepthSum : Nat
fiveSourceSlotGeometricDepthSum =
  TwoB.independentGeometricDepth TwoB.identitySlot
  + TwoB.independentGeometricDepth TwoB.minusOneSlot
  + TwoB.independentGeometricDepth TwoB.orderFourSlot
  + TwoB.independentGeometricDepth TwoB.orderThreeSlot
  + TwoB.independentGeometricDepth TwoB.orderSixSlot

sourceSlotGeometryAgreesWithClassDefectSum :
  fiveSourceSlotGeometricDepthSum ≡ fiveDefectSum
sourceSlotGeometryAgreesWithClassDefectSum = refl

sourceSlotGeometryIsNotSampledMassValuation :
  fiveSourceSlotGeometricDepthSum
    ≡ sampledWeightTwoAdicValuation -> ⊥
sourceSlotGeometryIsNotSampledMassValuation ()

------------------------------------------------------------------------
-- 4. No semantic promotion from inverse-centralizer weights.
------------------------------------------------------------------------

data RepresentativeSampleIsActualLoopReversalStackMass : Set where
data SumOfDefectsIsValuationOfSum : Set where
data GroupoidMassPaysCarnahanUranoDVRLength : Set where
data EitherMassComputesMonsterDefect : Set where

sampledWeightNotPromotedToQuotientStackMass :
  RepresentativeSampleIsActualLoopReversalStackMass -> ⊥
sampledWeightNotPromotedToQuotientStackMass ()

defectSumNotIdentifiedWithMassValuation :
  SumOfDefectsIsValuationOfSum -> ⊥
defectSumNotIdentifiedWithMassValuation ()

massNotPromotedToIntegralTateCompositionLength :
  GroupoidMassPaysCarnahanUranoDVRLength -> ⊥
massNotPromotedToIntegralTateCompositionLength ()

massNotPromotedToMonsterValuation :
  EitherMassComputesMonsterDefect -> ⊥
massNotPromotedToMonsterValuation ()

claimOrigin : Attribution.ClaimOrigin
claimOrigin = Attribution.repositoryCrossModuleInference

record P2InertiaMassVersusDefectBoundary : Set where
  constructor p2-inertia-mass-versus-defect-boundary
  field
    fullSevenClassMassIsOne : Bool
    sampledFiveWeightIsTwoThirds : Bool
    sampledFiveWeightHasV2One : Bool
    fullSevenClassWeightHasV2Zero : Bool
    fiveIndividualClassDefectsSumToTen : Bool
    sampledMassValuationEqualsDefectSum : Bool
    fullMassValuationEqualsDefectSum : Bool
    sampledWeightAssertedAsQuotientStackMass : Bool
    eitherWeightAssertedAsDVRLength : Bool
    externalMonsterCorrectionProved : Bool

canonicalP2InertiaMassVersusDefectBoundary :
  P2InertiaMassVersusDefectBoundary
canonicalP2InertiaMassVersusDefectBoundary =
  p2-inertia-mass-versus-defect-boundary
    true true true true true false false false false false
