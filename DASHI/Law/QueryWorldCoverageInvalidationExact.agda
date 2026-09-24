module DASHI.Law.QueryWorldCoverageInvalidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- S15 × S18: previously paid consumer coordinates are world-relative.
--
-- A coordinate paid in W₀ cannot be carried into W₁ when that exact required
-- coordinate changed.  Unrelated world changes preserve the payment.
------------------------------------------------------------------------

data Axis : Set where
  sourceRevision sourceSpan provenance temporal jurisdiction : Axis

data Payment : Axis → Set where
  paidSourceRevision : Payment sourceRevision
  paidSourceSpan : Payment sourceSpan
  paidProvenance : Payment provenance
  paidTemporal : Payment temporal
  paidJurisdiction : Payment jurisdiction

data WorldChange : Set where
  relevantSourceRevisionChange : WorldChange
  irrelevantSourceRevisionChange : WorldChange
  requiredTemporalChange : WorldChange
  unrequiredTemporalChange : WorldChange
  requiredJurisdictionChange : WorldChange
  unrequiredJurisdictionChange : WorldChange

data PaymentSurvives : WorldChange → Axis → Set where
  irrelevantRevisionKeepsSource :
    PaymentSurvives irrelevantSourceRevisionChange sourceRevision
  irrelevantRevisionKeepsSpan :
    PaymentSurvives irrelevantSourceRevisionChange sourceSpan
  irrelevantRevisionKeepsProvenance :
    PaymentSurvives irrelevantSourceRevisionChange provenance

  unrequiredTimeKeepsSource :
    PaymentSurvives unrequiredTemporalChange sourceRevision
  unrequiredTimeKeepsTime :
    PaymentSurvives unrequiredTemporalChange temporal

  unrequiredJurisdictionKeepsSource :
    PaymentSurvives unrequiredJurisdictionChange sourceRevision
  unrequiredJurisdictionKeepsJurisdiction :
    PaymentSurvives unrequiredJurisdictionChange jurisdiction

relevantRevisionInvalidatesSourceRevision :
  PaymentSurvives relevantSourceRevisionChange sourceRevision → ⊥
relevantRevisionInvalidatesSourceRevision ()

relevantRevisionInvalidatesSourceSpan :
  PaymentSurvives relevantSourceRevisionChange sourceSpan → ⊥
relevantRevisionInvalidatesSourceSpan ()

relevantRevisionInvalidatesProvenance :
  PaymentSurvives relevantSourceRevisionChange provenance → ⊥
relevantRevisionInvalidatesProvenance ()

requiredTimeInvalidatesTemporal :
  PaymentSurvives requiredTemporalChange temporal → ⊥
requiredTimeInvalidatesTemporal ()

requiredJurisdictionInvalidatesJurisdiction :
  PaymentSurvives requiredJurisdictionChange jurisdiction → ⊥
requiredJurisdictionInvalidatesJurisdiction ()

record QueryWorldCoverageInvalidationBoundary : Set where
  constructor queryWorldCoverageInvalidationBoundary
  field
    relevantRevisionInvalidatesSourcePayment : Bool
    relevantRevisionInvalidatesSourcePaymentIsTrue :
      relevantRevisionInvalidatesSourcePayment ≡ true

    relevantRevisionInvalidatesSpanPayment : Bool
    relevantRevisionInvalidatesSpanPaymentIsTrue :
      relevantRevisionInvalidatesSpanPayment ≡ true

    relevantRevisionInvalidatesProvenancePayment : Bool
    relevantRevisionInvalidatesProvenancePaymentIsTrue :
      relevantRevisionInvalidatesProvenancePayment ≡ true

    requiredTimeChangeInvalidatesTemporalPayment : Bool
    requiredTimeChangeInvalidatesTemporalPaymentIsTrue :
      requiredTimeChangeInvalidatesTemporalPayment ≡ true

    requiredJurisdictionChangeInvalidatesJurisdictionPayment : Bool
    requiredJurisdictionChangeInvalidatesJurisdictionPaymentIsTrue :
      requiredJurisdictionChangeInvalidatesJurisdictionPayment ≡ true

    irrelevantWorldChangeMayPreserveUnaffectedPayment : Bool
    irrelevantWorldChangeMayPreserveUnaffectedPaymentIsTrue :
      irrelevantWorldChangeMayPreserveUnaffectedPayment ≡ true

    invalidationCreatesSemanticAuthority : Bool
    invalidationCreatesSemanticAuthorityIsFalse :
      invalidationCreatesSemanticAuthority ≡ false

    invalidationCreatesClaimTruth : Bool
    invalidationCreatesClaimTruthIsFalse :
      invalidationCreatesClaimTruth ≡ false

open QueryWorldCoverageInvalidationBoundary public

canonicalQueryWorldCoverageInvalidationBoundary :
  QueryWorldCoverageInvalidationBoundary
canonicalQueryWorldCoverageInvalidationBoundary =
  queryWorldCoverageInvalidationBoundary
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
