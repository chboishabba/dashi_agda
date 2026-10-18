module DASHI.Law.SensibLawWave5ProfessionalHandoffCalibrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- M9 REAL WAVE-5 HANDOFF CALIBRATION
--
-- The ITIR fixture has three source layers:
--   clinic letter                  unreviewed
--   user journal account           unreviewed
--   therapist note                 reviewed
--
-- Review state and source class are preserved, but neither professional
-- authorship nor reviewed status supplies share scope automatically.
------------------------------------------------------------------------

data SourceLayer : Set where
  clinicLetter : SourceLayer
  userJournalAccount : SourceLayer
  therapistNote : SourceLayer

data ReviewState : Set where
  reviewed : ReviewState
  unreviewed : ReviewState

reviewState : SourceLayer → ReviewState
reviewState clinicLetter = unreviewed
reviewState userJournalAccount = unreviewed
reviewState therapistNote = reviewed

data SourceClass : SourceLayer → Set where
  documentaryThirdParty :
    SourceClass clinicLetter
  userAuthoredClientAccount :
    SourceClass userJournalAccount
  laterProfessionalInterpretation :
    SourceClass therapistNote

data ShareScopePaid : SourceLayer → Set where

data ProfessionalPayment : SourceLayer → Set where
  professionalPayment :
    ∀ {source} →
    reviewState source ≡ reviewed →
    ShareScopePaid source →
    ProfessionalPayment source

clinicCannotPayProfessional :
  ProfessionalPayment clinicLetter → ⊥
clinicCannotPayProfessional
  (professionalPayment () scope)

journalCannotPayProfessional :
  ProfessionalPayment userJournalAccount → ⊥
journalCannotPayProfessional
  (professionalPayment () scope)

therapistReviewAloneStillCannotPay :
  ProfessionalPayment therapistNote → ShareScopePaid therapistNote
therapistReviewAloneStillCannotPay
  (professionalPayment reviewedProof scope) = scope

data ReviewedProfessionalSourceAutomaticallyShared : Set where
data SourceClassCreatesAuthority : Set where
data HandoffCreatesClaimTruth : Set where

reviewedProfessionalSourceDoesNotAutoShare :
  ReviewedProfessionalSourceAutomaticallyShared → ⊥
reviewedProfessionalSourceDoesNotAutoShare ()

sourceClassDoesNotCreateAuthority :
  SourceClassCreatesAuthority → ⊥
sourceClassDoesNotCreateAuthority ()

handoffDoesNotCreateTruth :
  HandoffCreatesClaimTruth → ⊥
handoffDoesNotCreateTruth ()

record Wave5ProfessionalHandoffBoundary : Set where
  constructor wave5ProfessionalHandoffBoundary
  field
    clinicRemainsUnreviewed : Bool
    clinicRemainsUnreviewedIsTrue :
      clinicRemainsUnreviewed ≡ true

    journalRemainsUnreviewed : Bool
    journalRemainsUnreviewedIsTrue :
      journalRemainsUnreviewed ≡ true

    therapistLayerIsReviewed : Bool
    therapistLayerIsReviewedIsTrue :
      therapistLayerIsReviewed ≡ true

    reviewedTherapistLayerAutomaticallyShared : Bool
    reviewedTherapistLayerAutomaticallySharedIsFalse :
      reviewedTherapistLayerAutomaticallyShared ≡ false

    sourceClassCreatesAuthority : Bool
    sourceClassCreatesAuthorityIsFalse :
      sourceClassCreatesAuthority ≡ false

    handoffCreatesClaimTruth : Bool
    handoffCreatesClaimTruthIsFalse :
      handoffCreatesClaimTruth ≡ false

open Wave5ProfessionalHandoffBoundary public

canonicalWave5ProfessionalHandoffBoundary :
  Wave5ProfessionalHandoffBoundary
canonicalWave5ProfessionalHandoffBoundary =
  wave5ProfessionalHandoffBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
