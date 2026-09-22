module DASHI.Law.SensibLawWave5ShareScopeReceiptExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- M9 WAVE-5 EXPLICIT SHARE-SCOPE RECEIPT
--
-- Review and share scope are distinct receipts.
-- The reviewed therapist-note coordinate cannot enter any professional fibre
-- without a separate explicit scope witness.
------------------------------------------------------------------------

data Coordinate : Set where
  therapistNote : Coordinate
  clinicLetter : Coordinate
  userJournalAccount : Coordinate

data Consumer : Set where
  lawyer : Consumer
  doctor : Consumer
  advocate : Consumer
  regulator : Consumer

data Reviewed : Coordinate → Set where
  therapistReviewed : Reviewed therapistNote

data ScopeDecision : Coordinate → Consumer → Set where
  allow :
    ∀ {coordinate consumer} →
    Reviewed coordinate →
    ScopeDecision coordinate consumer
  deny :
    ∀ {coordinate consumer} →
    ScopeDecision coordinate consumer
  notReady :
    ∀ {coordinate consumer} →
    ScopeDecision coordinate consumer
  withdrawn :
    ∀ {coordinate consumer} →
    ScopeDecision coordinate consumer

data Included : Coordinate → Consumer → Set where
  includeAfterAllow :
    ∀ {coordinate consumer} →
    Reviewed coordinate →
    ScopeDecision coordinate consumer →
    Included coordinate consumer

------------------------------------------------------------------------
-- Unreviewed real Wave-5 rows cannot become professional payments.
------------------------------------------------------------------------

clinicCannotBeReviewed :
  Reviewed clinicLetter → ⊥
clinicCannotBeReviewed ()

journalCannotBeReviewed :
  Reviewed userJournalAccount → ⊥
journalCannotBeReviewed ()

clinicCannotBeIncluded :
  Included clinicLetter lawyer → ⊥
clinicCannotBeIncluded
  (includeAfterAllow () scope)

journalCannotBeIncluded :
  Included userJournalAccount lawyer → ⊥
journalCannotBeIncluded
  (includeAfterAllow () scope)

------------------------------------------------------------------------
-- Review alone is insufficient.
------------------------------------------------------------------------

data ReviewAloneCreatesScope : Set where
data ProfessionalAuthorshipCreatesScope : Set where
data ScopeCreatesSemanticAuthority : Set where
data ScopeCreatesClaimTruth : Set where

reviewAloneCannotCreateScope :
  ReviewAloneCreatesScope → ⊥
reviewAloneCannotCreateScope ()

professionalAuthorshipCannotCreateScope :
  ProfessionalAuthorshipCreatesScope → ⊥
professionalAuthorshipCannotCreateScope ()

scopeDoesNotCreateAuthority :
  ScopeCreatesSemanticAuthority → ⊥
scopeDoesNotCreateAuthority ()

scopeDoesNotCreateTruth :
  ScopeCreatesClaimTruth → ⊥
scopeDoesNotCreateTruth ()

------------------------------------------------------------------------
-- Test-only witness surface.
--
-- These witnesses prove the generic property that distinct professional fibres
-- can be produced from one reviewed coordinate. They are not user consent and
-- are not governance decisions about the real Wave-5 material.
------------------------------------------------------------------------

testOnlyTherapistLawyerAllow :
  ScopeDecision therapistNote lawyer
testOnlyTherapistLawyerAllow =
  allow therapistReviewed

testOnlyTherapistDoctorDeny :
  ScopeDecision therapistNote doctor
testOnlyTherapistDoctorDeny =
  deny

testOnlyLawyerInclusion :
  Included therapistNote lawyer
testOnlyLawyerInclusion =
  includeAfterAllow
    therapistReviewed
    testOnlyTherapistLawyerAllow

data Recompute : Consumer → Coordinate → Set where
  becauseIncluded :
    ∀ {consumer coordinate} →
    Included coordinate consumer →
    Recompute consumer coordinate

testOnlyTherapistDeltaReopensLawyer :
  Recompute lawyer therapistNote
testOnlyTherapistDeltaReopensLawyer =
  becauseIncluded testOnlyLawyerInclusion

doctorDeniedDoesNotRecompute :
  Recompute doctor therapistNote → ⊥
doctorDeniedDoesNotRecompute
  (becauseIncluded (includeAfterAllow reviewed scope)) with scope
... | allow reviewed' = ⊥-elim (reviewAloneCannotCreateScope ())
... | deny = λ ()
... | notReady = λ ()
... | withdrawn = λ ()

record Wave5ShareScopeBoundary : Set where
  constructor wave5ShareScopeBoundary
  field
    reviewAndShareAreDistinct : Bool
    reviewAndShareAreDistinctIsTrue :
      reviewAndShareAreDistinct ≡ true

    unreviewedRowsCannotBeAllowed : Bool
    unreviewedRowsCannotBeAllowedIsTrue :
      unreviewedRowsCannotBeAllowed ≡ true

    reviewedTherapistRequiresSeparateScope : Bool
    reviewedTherapistRequiresSeparateScopeIsTrue :
      reviewedTherapistRequiresSeparateScope ≡ true

    testOnlyDistinctFibresExist : Bool
    testOnlyDistinctFibresExistIsTrue :
      testOnlyDistinctFibresExist ≡ true

    scopeCreatesSemanticAuthority : Bool
    scopeCreatesSemanticAuthorityIsFalse :
      scopeCreatesSemanticAuthority ≡ false

    scopeCreatesClaimTruth : Bool
    scopeCreatesClaimTruthIsFalse :
      scopeCreatesClaimTruth ≡ false

open Wave5ShareScopeBoundary public

canonicalWave5ShareScopeBoundary :
  Wave5ShareScopeBoundary
canonicalWave5ShareScopeBoundary =
  wave5ShareScopeBoundary
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
