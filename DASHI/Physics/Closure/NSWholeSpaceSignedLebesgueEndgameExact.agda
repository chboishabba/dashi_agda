module DASHI.Physics.Closure.NSWholeSpaceSignedLebesgueEndgameExact where

------------------------------------------------------------------------
-- WHOLE-SPACE A / SHARED-SIGNED-CORE LEBESGUE ENDGAME
--
-- A now has the canonical continuous convolution carrier, the signed
-- centered-resolvent split, the low-frequency compensation order, and the
-- monotone/dominated Lebesgue compiler.  This owner packages those pieces into
-- one continuation object without deriving A from periodic B.
--
-- The remaining analytic producer is intentionally explicit:
-- construct the physical compensated second-moment field on the actual
-- Euclidean Fourier trajectory and prove its majorant integrable.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSTriadKNSignedFrequencyCarrierExact as Core
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean
import DASHI.Physics.Closure.NSTriadKNEuclideanLebesgueSignedAggregationExact as Lebesgue
import DASHI.Physics.Closure.NSLebesgueSignedSecondMomentAggregationExact as Second

record WholeSpaceSignedLebesgueEndgame
    (dataSet : Euclidean.EuclideanSignedFluxData)
    (base : Lebesgue.EuclideanLebesgueIntegralAuthority dataSet)
    : Set₁ where
  field
    convolutionMeasure :
      Lebesgue.EuclideanConvolutionMeasureAuthority

    orderedIntegral :
      Second.OrderedEuclideanLebesgueAuthority base

    compensatedField :
      Second.LowFrequencySecondMomentField base

open WholeSpaceSignedLebesgueEndgame public

wholeSpaceSignedCenteredResolventSplit :
  ∀ {dataSet base} →
  WholeSpaceSignedLebesgueEndgame dataSet base →
  let
    C = Euclidean.euclideanSignedFrequencyCarrier dataSet
    A = Lebesgue.euclideanLebesgueAggregation dataSet base
  in
  Core.aggregate A (Core.weightedFlux C)
  ≡
  Core._minus_ C
    (Core.aggregate A (Core.commonResolventFlux C))
    (Core.aggregate A (Core.centeredResolventCorrection C))
wholeSpaceSignedCenteredResolventSplit {dataSet} {base} E =
  Lebesgue.euclideanLebesgueCenteredResolventSplit dataSet base

wholeSpaceCompensatedSecondMomentBound :
  ∀ {dataSet base}
    (E : WholeSpaceSignedLebesgueEndgame dataSet base) →
  BishopReal._≤_
    (Lebesgue.integral base
      (Second.compensatedSecondMomentIntegrand
        (compensatedField E)))
    (Lebesgue.integral base
      (Second.compensatedSecondMomentMajorant
        (compensatedField E)))
wholeSpaceCompensatedSecondMomentBound E =
  Second.integratedCompensatedSecondMomentBound
    (orderedIntegral E)
    (compensatedField E)

------------------------------------------------------------------------
-- Machine-readable frontier.
------------------------------------------------------------------------

wholeSpaceSignedCoreRealized : Bool
wholeSpaceSignedCoreRealized = true

wholeSpaceLebesgueAggregationCompilerClosed : Bool
wholeSpaceLebesgueAggregationCompilerClosed = true

wholeSpaceLowFrequencyCompensationBeforeIntegrationClosed : Bool
wholeSpaceLowFrequencyCompensationBeforeIntegrationClosed = true

physicalCompensatedMajorantProducerConstructedHere : Bool
physicalCompensatedMajorantProducerConstructedHere = false

periodicProofUsedToDeriveWholeSpace : Bool
periodicProofUsedToDeriveWholeSpace = false

clayPromotion : Bool
clayPromotion = false

wholeSpaceSignedCoreRealizedIsTrue :
  wholeSpaceSignedCoreRealized ≡ true
wholeSpaceSignedCoreRealizedIsTrue = refl

wholeSpaceLebesgueAggregationCompilerClosedIsTrue :
  wholeSpaceLebesgueAggregationCompilerClosed ≡ true
wholeSpaceLebesgueAggregationCompilerClosedIsTrue = refl

periodicProofUsedToDeriveWholeSpaceIsFalse :
  periodicProofUsedToDeriveWholeSpace ≡ false
periodicProofUsedToDeriveWholeSpaceIsFalse = refl

physicalCompensatedMajorantProducerConstructedHereIsFalse :
  physicalCompensatedMajorantProducerConstructedHere ≡ false
physicalCompensatedMajorantProducerConstructedHereIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
