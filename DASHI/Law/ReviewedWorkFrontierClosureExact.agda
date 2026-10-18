module DASHI.Law.ReviewedWorkFrontierClosureExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Reviewed work pays its own frontier obligation.
--
-- Accepting a reviewed identity/treatment delta may expose secondary
-- consequences, but the exact work just paid must not be reintroduced as a
-- fresh acquisition/review demand.  Separately, an empty selectable frontier
-- is an operational closure statement only; it is not a proof of consumer
-- adequacy, legal authority, or current-law truth.
------------------------------------------------------------------------

data ReviewedWorkKind : Set where
  reviewedIdentity : ReviewedWorkKind
  reviewedTreatment : ReviewedWorkKind

data FrontierDisposition : Set where
  frontierOpen : FrontierDisposition
  noSelectableResidual : FrontierDisposition
  budgetExhausted : FrontierDisposition

paidWorkReappearsFresh : ReviewedWorkKind → Bool
paidWorkReappearsFresh reviewedIdentity = false
paidWorkReappearsFresh reviewedTreatment = false

reviewedIdentityDoesNotResurrect :
  paidWorkReappearsFresh reviewedIdentity ≡ false
reviewedIdentityDoesNotResurrect = refl

reviewedTreatmentDoesNotResurrect :
  paidWorkReappearsFresh reviewedTreatment ≡ false
reviewedTreatmentDoesNotResurrect = refl

record ReviewedWorkFrontierClosureBoundary : Set where
  constructor reviewedWorkFrontierClosureBoundary
  field
    acceptedReviewedIdentityMayReopenItselfAsFreshSource : Bool
    acceptedReviewedIdentityMayReopenItselfAsFreshSourceIsFalse :
      acceptedReviewedIdentityMayReopenItselfAsFreshSource ≡ false

    acceptedReviewedTreatmentMayReopenItselfAsFreshTreatment : Bool
    acceptedReviewedTreatmentMayReopenItselfAsFreshTreatmentIsFalse :
      acceptedReviewedTreatmentMayReopenItselfAsFreshTreatment ≡ false

    paidWorkMayExposeSecondaryConsequences : Bool
    paidWorkMayExposeSecondaryConsequencesIsTrue :
      paidWorkMayExposeSecondaryConsequences ≡ true

    noSelectableResidualMeansCurrentFrontierClosed : Bool
    noSelectableResidualMeansCurrentFrontierClosedIsTrue :
      noSelectableResidualMeansCurrentFrontierClosed ≡ true

    currentFrontierClosedImpliesConsumerAdequacyProved : Bool
    currentFrontierClosedImpliesConsumerAdequacyProvedIsFalse :
      currentFrontierClosedImpliesConsumerAdequacyProved ≡ false

    currentFrontierClosedCreatesLegalAuthority : Bool
    currentFrontierClosedCreatesLegalAuthorityIsFalse :
      currentFrontierClosedCreatesLegalAuthority ≡ false

    currentFrontierClosedCreatesCurrentLawConclusion : Bool
    currentFrontierClosedCreatesCurrentLawConclusionIsFalse :
      currentFrontierClosedCreatesCurrentLawConclusion ≡ false

open ReviewedWorkFrontierClosureBoundary public

canonicalReviewedWorkFrontierClosureBoundary :
  ReviewedWorkFrontierClosureBoundary
canonicalReviewedWorkFrontierClosureBoundary =
  reviewedWorkFrontierClosureBoundary
    false refl
    false refl
    true refl
    true refl
    false refl
    false refl
    false refl

data PaidTreatmentAutomaticallyFreshTreatment : Set where
data FrontierClosedAutomaticallyConsumerAdequate : Set where
data FrontierClosedAutomaticallyAuthority : Set where

paidTreatmentCannotAutomaticallyReappearFresh :
  PaidTreatmentAutomaticallyFreshTreatment → ⊥
paidTreatmentCannotAutomaticallyReappearFresh ()

frontierClosureDoesNotProveConsumerAdequacy :
  FrontierClosedAutomaticallyConsumerAdequate → ⊥
frontierClosureDoesNotProveConsumerAdequacy ()

frontierClosureDoesNotCreateAuthority :
  FrontierClosedAutomaticallyAuthority → ⊥
frontierClosureDoesNotCreateAuthority ()
