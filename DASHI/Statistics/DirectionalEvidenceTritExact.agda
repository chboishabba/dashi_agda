module DASHI.Statistics.DirectionalEvidenceTritExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.Trit as Trit
import DASHI.Codec.BalancedTritBitFibre as Bits

------------------------------------------------------------------------
-- DIRECTIONAL EVIDENCE OVER THE CANONICAL BALANCED TRIT
--
-- Conventional balanced three-valued ordering:
--   negative / false-like direction = -1
--   unresolved / indeterminate      =  0
--   positive / true-like direction  = +1
--
-- The semantics are proposition- and design-indexed.  The trit is the carrier;
-- it does not decide what counts as positive or negative evidence.
------------------------------------------------------------------------

record DirectionalInferenceSemantics (Result Hypothesis : Set) : Set₁ where
  constructor directionalInferenceSemantics
  field
    SupportsPositive : Result → Hypothesis → Set
    Underdetermined : Result → Hypothesis → Set
    SupportsNegative : Result → Hypothesis → Set
    semanticsReference : String
open DirectionalInferenceSemantics public

data DirectionalEvidence
    {Result Hypothesis : Set}
    (semantics : DirectionalInferenceSemantics Result Hypothesis)
    (result : Result)
    (hypothesis : Hypothesis) : Trit.Trit → Set where
  negativeEvidence :
    SupportsNegative semantics result hypothesis →
    DirectionalEvidence semantics result hypothesis Trit.neg
  underdeterminedEvidence :
    Underdetermined semantics result hypothesis →
    DirectionalEvidence semantics result hypothesis Trit.zer
  positiveEvidence :
    SupportsPositive semantics result hypothesis →
    DirectionalEvidence semantics result hypothesis Trit.pos

------------------------------------------------------------------------
-- Failure-to-establish and counterevidence are different typed objects.
------------------------------------------------------------------------

record FailToEstablishPositive
    {Result Hypothesis : Set}
    (semantics : DirectionalInferenceSemantics Result Hypothesis)
    (result : Result)
    (hypothesis : Hypothesis) : Set₁ where
  constructor failToEstablishPositive
  field
    PositiveReceipt : Set
    noPositiveReceipt : PositiveReceipt → ⊥
    failureReference : String
open FailToEstablishPositive public

record NegativeEvidenceReceipt
    {Result Hypothesis : Set}
    (semantics : DirectionalInferenceSemantics Result Hypothesis)
    (result : Result)
    (hypothesis : Hypothesis) : Set where
  constructor negativeEvidenceReceipt
  field
    negativeWitness : SupportsNegative semantics result hypothesis
open NegativeEvidenceReceipt public

negativeReceiptCompilesToNeg :
  ∀ {Result Hypothesis semantics result hypothesis} →
  NegativeEvidenceReceipt {Result} {Hypothesis} semantics result hypothesis →
  DirectionalEvidence semantics result hypothesis Trit.neg
negativeReceiptCompilesToNeg receipt = negativeEvidence (negativeWitness receipt)

-- Structural firewall: no constructor inhabits this permission merely from a
-- failed positive search.  Domain adapters must instead supply the explicit
-- NegativeEvidenceReceipt above.
data FailureAloneAuthorizesNegative : Set where

failureAloneDoesNotAuthorizeNegative : FailureAloneAuthorizesNegative → ⊥
failureAloneDoesNotAuthorizeNegative ()

------------------------------------------------------------------------
-- Existing exact ternary-in-binary fibre retained.
------------------------------------------------------------------------

directionalBitView : Trit.Trit → Bits.BitStreamView
directionalBitView = Bits.bitStreamView

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

record DirectionalEvidenceBoundary : Set where
  constructor directionalEvidenceBoundary
  field
    negativeMapsToMinusOne : Bool
    underdeterminedMapsToZero : Bool
    positiveMapsToPlusOne : Bool
    zeroMeansNegativeEvidence : Bool
    failedPositiveSearchAutomaticallyMeansNegative : Bool
    negativePromotionRequiresNegativeWitness : Bool
    binaryPresentationChangesDirectionalSemantics : Bool

canonicalDirectionalEvidenceBoundary : DirectionalEvidenceBoundary
canonicalDirectionalEvidenceBoundary =
  directionalEvidenceBoundary true true true false false true false
