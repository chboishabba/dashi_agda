module DASHI.Physics.Closure.NSTriadKNEuclideanLebesgueSignedAggregationExact where

------------------------------------------------------------------------
-- WHOLE-SPACE LEBESGUE AGGREGATION FOR THE SIGNED FREQUENCY CORE
--
-- This is the continuous counterpart of the periodic finite/counting fold.
-- It does not fake a concrete measure implementation.  Instead it isolates the
-- exact theorem-bearing analysis authority needed from the repository's
-- Bishop/Lebesgue layer:
--
--   * integrability of the selected observable;
--   * extensionality of the integral;
--   * signed linearity.
--
-- Once those laws are supplied for the actual R^3 x R^3 convolution
-- interaction, the generic aggregateCenteredResolventSplit theorem applies
-- verbatim.  No T^3 -> R^3 sum-to-integral limit is used.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import Real as BishopReal

import DASHI.Physics.Closure.NSTriadKNSignedFrequencyCarrierExact as Core
import DASHI.Physics.Closure.NSTriadKNEuclideanSignedFrequencyCarrierRealizationExact as Euclidean

record EuclideanLebesgueIntegralAuthority
    (dataSet : Euclidean.EuclideanSignedFluxData) : Set₁ where
  field
    Integrable :
      (Euclidean.EuclideanInteraction → BishopReal.ℝ) → Set

    integral :
      (Euclidean.EuclideanInteraction → BishopReal.ℝ) → BishopReal.ℝ

    weightedFluxIntegrable :
      Integrable (Euclidean.weightedFluxR3 dataSet)

    commonResolventFluxIntegrable :
      Integrable (Euclidean.commonResolventFluxR3 dataSet)

    centeredCorrectionIntegrable :
      Integrable (Euclidean.centeredResolventCorrectionR3 dataSet)

    integralRespectsPointwise :
      {f g : Euclidean.EuclideanInteraction → BishopReal.ℝ} →
      ((x : Euclidean.EuclideanInteraction) → f x ≡ g x) →
      integral f ≡ integral g

    integralDifference :
      (f g : Euclidean.EuclideanInteraction → BishopReal.ℝ) →
      integral
        (λ x → BishopReal._-_ (f x) (g x))
      ≡
      BishopReal._-_ (integral f) (integral g)

open EuclideanLebesgueIntegralAuthority public

euclideanLebesgueAggregation :
  (dataSet : Euclidean.EuclideanSignedFluxData) →
  EuclideanLebesgueIntegralAuthority dataSet →
  Core.SignedFrequencyAggregation
    (Euclidean.euclideanSignedFrequencyCarrier dataSet)
euclideanLebesgueAggregation dataSet authority = record
  { Core.aggregate = integral authority
  ; Core.aggregateRespectsPointwise =
      integralRespectsPointwise authority
  ; Core.aggregateDifference =
      integralDifference authority
  }

euclideanLebesgueCenteredResolventSplit :
  (dataSet : Euclidean.EuclideanSignedFluxData) →
  (authority : EuclideanLebesgueIntegralAuthority dataSet) →
  let
    C = Euclidean.euclideanSignedFrequencyCarrier dataSet
    A = euclideanLebesgueAggregation dataSet authority
  in
  Core.aggregate A (Core.weightedFlux C)
  ≡
  Core._minus_ C
    (Core.aggregate A (Core.commonResolventFlux C))
    (Core.aggregate A (Core.centeredResolventCorrection C))
euclideanLebesgueCenteredResolventSplit dataSet authority =
  Core.aggregateCenteredResolventSplit
    (Euclidean.euclideanSignedFrequencyCarrier dataSet)
    (euclideanLebesgueAggregation dataSet authority)

------------------------------------------------------------------------
-- Fubini/change-of-variable are separate because the generic signed theorem
-- does not need them.  They are needed only when identifying this abstract
-- integral with the conventional
--
--   integral_xi integral_eta F(xi,eta,xi-eta) d eta d xi
--
-- representation.
------------------------------------------------------------------------

record EuclideanConvolutionMeasureAuthority : Set₁ where
  field
    FibreIntegrable : Set
    FubiniForSelectedConvolution : Set
    translationChangeOfVariableEtaToXiMinusEta : Set
    jacobianOneForTranslation : Set
    differentiationUnderSelectedIntegral : Set

lebesgueSignedAggregationCompilerClosed : Bool
lebesgueSignedAggregationCompilerClosed = true

concreteLebesgueMeasureConstructionClosedHere : Bool
concreteLebesgueMeasureConstructionClosedHere = false

fubiniAutomaticallyNeededForPointwiseSplit : Bool
fubiniAutomaticallyNeededForPointwiseSplit = false

torusLimitUsed : Bool
torusLimitUsed = false

clayPromotion : Bool
clayPromotion = false

lebesgueSignedAggregationCompilerClosedIsTrue :
  lebesgueSignedAggregationCompilerClosed ≡ true
lebesgueSignedAggregationCompilerClosedIsTrue = refl

torusLimitUsedIsFalse : torusLimitUsed ≡ false
torusLimitUsedIsFalse = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
