module DASHI.Law.SensibLawYindjibarndiPartyComparativeWorldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.SensibLawYindjibarndiEmpiricalAuthorityJoinExact as Y
import DASHI.Law.SensibLawYindjibarndiAdversarialRerunExact as Rerun

------------------------------------------------------------------------
-- M11 / S26.6 ADVERSARIAL-PARTY COMPARISON
--
-- This compares reviewed party treatments without ranking parties or turning
-- submissions into holdings. Shared authority identity may coexist with
-- opposed role/treatment of that authority.
------------------------------------------------------------------------

data Party : Set where
  applicant : Party
  stateOfWesternAustralia : Party
  fmgRespondents : Party

data AuthorityCoordinate : Set where
  yunupinguAcquisition : AuthorityCoordinate
  maboAcquisitionDistinction : AuthorityCoordinate

data PartyTreatment : Party → AuthorityCoordinate → Set where
  applicantYunupingu :
    PartyTreatment applicant yunupinguAcquisition
  stateYunupingu :
    PartyTreatment stateOfWesternAustralia yunupinguAcquisition
  fmgYunupingu :
    PartyTreatment fmgRespondents yunupinguAcquisition
  applicantMabo :
    PartyTreatment applicant maboAcquisitionDistinction
  fmgMabo :
    PartyTreatment fmgRespondents maboAcquisitionDistinction

data TreatmentRole : Set where
  supportRole : TreatmentRole
  defeaterRole : TreatmentRole
  counterDefeaterRole : TreatmentRole
  authorityScopeRole : TreatmentRole

treatmentRole :
  ∀ {party coordinate} →
  PartyTreatment party coordinate →
  TreatmentRole
treatmentRole applicantYunupingu = supportRole
treatmentRole stateYunupingu = authorityScopeRole
treatmentRole fmgYunupingu = defeaterRole
treatmentRole applicantMabo = counterDefeaterRole
treatmentRole fmgMabo = defeaterRole

------------------------------------------------------------------------
-- Shared coordinate, different treatment.
------------------------------------------------------------------------

applicantAndStateShareYunupinguCoordinate :
  PartyTreatment applicant yunupinguAcquisition
  × PartyTreatment stateOfWesternAustralia yunupinguAcquisition
applicantAndStateShareYunupinguCoordinate =
  applicantYunupingu , stateYunupingu

applicantAndStateTreatYunupinguDifferently :
  treatmentRole applicantYunupingu
    ≡ treatmentRole stateYunupingu → ⊥
applicantAndStateTreatYunupinguDifferently ()

applicantAndFmgShareMaboCoordinate :
  PartyTreatment applicant maboAcquisitionDistinction
  × PartyTreatment fmgRespondents maboAcquisitionDistinction
applicantAndFmgShareMaboCoordinate =
  applicantMabo , fmgMabo

applicantAndFmgTreatMaboDifferently :
  treatmentRole applicantMabo
    ≡ treatmentRole fmgMabo → ⊥
applicantAndFmgTreatMaboDifferently ()

------------------------------------------------------------------------
-- Reuse exact empirical packet and rerun boundaries.
------------------------------------------------------------------------

opposingTreatmentsAlreadyCoexist :
  Y.opposingAuthorityTreatmentsCoexist
    Y.canonicalYindjibarndiEmpiricalJoinBoundary
  ≡ true
opposingTreatmentsAlreadyCoexist = refl

routeStateStillDoesNotPredictOutcome :
  Rerun.routeStatePredictsJudicialOutcome
    Rerun.canonicalYindjibarndiRerunBoundary
  ≡ false
routeStateStillDoesNotPredictOutcome = refl

data SharedAuthorityMeansSameLegalPosition : Set where
data SubmissionAutomaticallyBecomesHolding : Set where
data PartyComparisonSelectsWinner : Set where
data PartyComparisonPredictsOutcome : Set where
data DifferentTreatmentCreatesDifferentAuthorityIdentity : Set where

sharedAuthorityDoesNotCollapsePositions :
  SharedAuthorityMeansSameLegalPosition → ⊥
sharedAuthorityDoesNotCollapsePositions ()

submissionDoesNotBecomeHolding :
  SubmissionAutomaticallyBecomesHolding → ⊥
submissionDoesNotBecomeHolding ()

partyComparisonDoesNotSelectWinner :
  PartyComparisonSelectsWinner → ⊥
partyComparisonDoesNotSelectWinner ()

partyComparisonDoesNotPredictOutcome :
  PartyComparisonPredictsOutcome → ⊥
partyComparisonDoesNotPredictOutcome ()

differentTreatmentDoesNotDuplicateAuthority :
  DifferentTreatmentCreatesDifferentAuthorityIdentity → ⊥
differentTreatmentDoesNotDuplicateAuthority ()

record YindjibarndiPartyComparativeBoundary : Set where
  constructor yindjibarndiPartyComparativeBoundary
  field
    sameAuthorityMayHaveOpposedTreatment : Bool
    sameAuthorityMayHaveOpposedTreatmentIsTrue :
      sameAuthorityMayHaveOpposedTreatment ≡ true

    applicantStateYunupinguRolesDiffer : Bool
    applicantStateYunupinguRolesDifferIsTrue :
      applicantStateYunupinguRolesDiffer ≡ true

    applicantFmgMaboRolesDiffer : Bool
    applicantFmgMaboRolesDifferIsTrue :
      applicantFmgMaboRolesDiffer ≡ true

    submissionsBecomeHoldings : Bool
    submissionsBecomeHoldingsIsFalse :
      submissionsBecomeHoldings ≡ false

    comparisonSelectsWinner : Bool
    comparisonSelectsWinnerIsFalse :
      comparisonSelectsWinner ≡ false

    comparisonPredictsOutcome : Bool
    comparisonPredictsOutcomeIsFalse :
      comparisonPredictsOutcome ≡ false

open YindjibarndiPartyComparativeBoundary public

canonicalYindjibarndiPartyComparativeBoundary :
  YindjibarndiPartyComparativeBoundary
canonicalYindjibarndiPartyComparativeBoundary =
  yindjibarndiPartyComparativeBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
