module DASHI.Statistics.DirectionalInferenceDesignExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Statistics.DirectionalEvidenceTritExact as Directional
import DASHI.Statistics.Vec15Inference as Vec15

------------------------------------------------------------------------
-- DESIGN-RELATIVE DIRECTIONAL INFERENCE
--
-- A negative conclusion is not the complement of failing a positive test.
-- It requires a declared negative claim/region and a design-relative witness
-- that the observation lies in the corresponding support region.
------------------------------------------------------------------------

record DirectionalDesign : Set₁ where
  constructor directionalDesign
  field
    Result Hypothesis ClaimRegion : Set
    positiveRegion : Hypothesis → ClaimRegion
    negativeRegion : Hypothesis → ClaimRegion
    unresolvedRegion : Hypothesis → ClaimRegion
    observationRegion : Result → ClaimRegion
    SupportsPositive : Result → Hypothesis → Set
    SupportsNegative : Result → Hypothesis → Set
    Underdetermined : Result → Hypothesis → Set
    nuisanceHandled : Result → Set
    calibrationValid : Result → Set
    designReference : String
open DirectionalDesign public

semanticsFromDesign : (design : DirectionalDesign) →
  Directional.DirectionalInferenceSemantics (Result design) (Hypothesis design)
semanticsFromDesign design =
  Directional.directionalInferenceSemantics
    (SupportsPositive design)
    (Underdetermined design)
    (SupportsNegative design)
    (designReference design)

record NegativeDesignReceipt
    (design : DirectionalDesign)
    (result : Result design)
    (hypothesis : Hypothesis design) : Set where
  constructor negativeDesignReceipt
  field
    supportsNegative : SupportsNegative design result hypothesis
    nuisanceReceipt : nuisanceHandled design result
    calibrationReceipt : calibrationValid design result
    receiptReference : String
open NegativeDesignReceipt public

compileNegativeDesignReceipt :
  ∀ {design result hypothesis} →
  NegativeDesignReceipt design result hypothesis →
  Directional.NegativeEvidenceReceipt
    (semanticsFromDesign design) result hypothesis
compileNegativeDesignReceipt receipt =
  Directional.negativeEvidenceReceipt (supportsNegative receipt)

------------------------------------------------------------------------
-- EXISTING VEC15 DECISION SURFACE IS NOT DIRECTIONAL EVIDENCE
------------------------------------------------------------------------

data Vec15NegativePromotionPermission : Vec15.Decision → Set where
  rejectMayNeedDirectionalInterpretation :
    Vec15NegativePromotionPermission Vec15.reject

failToRejectDoesNotCarryNegativePromotion :
  Vec15NegativePromotionPermission Vec15.failToReject → ⊥
failToRejectDoesNotCarryNegativePromotion ()

record DirectionalInferenceDesignBoundary : Set where
  constructor directionalInferenceDesignBoundary
  field
    failToRejectAutomaticallyMeansNegativeEvidence : Bool
    negativeEvidenceRequiresDeclaredNegativeRegion : Bool
    negativeEvidenceRequiresDesignReceipt : Bool
    testDecisionEqualsDirectionalInterpretation : Bool
    equivalenceClaimEqualsNegativeDirectionClaim : Bool

canonicalDirectionalInferenceDesignBoundary : DirectionalInferenceDesignBoundary
canonicalDirectionalInferenceDesignBoundary =
  directionalInferenceDesignBoundary false true true false false
