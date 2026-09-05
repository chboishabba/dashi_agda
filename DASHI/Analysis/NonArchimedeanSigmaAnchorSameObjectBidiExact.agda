module DASHI.Analysis.NonArchimedeanSigmaAnchorSameObjectBidiExact where

------------------------------------------------------------------------
-- SIGMA ANCHOR SAME-OBJECT BIDI
--
-- The local cyclotomic condition and the Prolate critical-line condition are
-- not promoted merely because both select the numeral 1/2.  A genuine anchor
-- theorem must identify their parameter carriers and preserve the conditions
-- that make the selected value distinguished.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

record SigmaAnchorSameObject : Set₂ where
  field
    CyclotomicSigma ProlateSigma : Set

    toProlate : CyclotomicSigma → ProlateSigma
    fromProlate : ProlateSigma → CyclotomicSigma

    roundTripCyclotomic :
      (sigma : CyclotomicSigma) →
      fromProlate (toProlate sigma) ≡ sigma

    roundTripProlate :
      (sigma : ProlateSigma) →
      toProlate (fromProlate sigma) ≡ sigma

    cyclotomicAnchorCondition : CyclotomicSigma → Set
    prolateCriticalCondition : ProlateSigma → Set

    anchorToCritical :
      (sigma : CyclotomicSigma) →
      cyclotomicAnchorCondition sigma →
      prolateCriticalCondition (toProlate sigma)

    criticalToAnchor :
      (sigma : ProlateSigma) →
      prolateCriticalCondition sigma →
      cyclotomicAnchorCondition (fromProlate sigma)

open SigmaAnchorSameObject public

record SigmaAnchorPromotionBoundary : Set where
  constructor sigmaAnchorPromotionBoundary
  field
    bothConditionsSelectHalfIsEnough : Bool
    commonSemilocalTensorCarrierIsEnough : Bool
    twoSidedParameterRechartRequired : Bool
    conditionPreservationBothDirectionsRequired : Bool
    sourceSameObjectWeldLocated : Bool

canonicalSigmaAnchorPromotionBoundary : SigmaAnchorPromotionBoundary
canonicalSigmaAnchorPromotionBoundary =
  sigmaAnchorPromotionBoundary false false true true false

sameNumeralCannotSubstituteForWeld :
  SigmaAnchorPromotionBoundary.bothConditionsSelectHalfIsEnough
    canonicalSigmaAnchorPromotionBoundary
  ≡ false
sameNumeralCannotSubstituteForWeld = refl

commonTensorCarrierCannotSubstituteForWeld :
  SigmaAnchorPromotionBoundary.commonSemilocalTensorCarrierIsEnough
    canonicalSigmaAnchorPromotionBoundary
  ≡ false
commonTensorCarrierCannotSubstituteForWeld = refl

sourceAnchorWeldStillLive :
  SigmaAnchorPromotionBoundary.sourceSameObjectWeldLocated
    canonicalSigmaAnchorPromotionBoundary
  ≡ false
sourceAnchorWeldStillLive = refl
