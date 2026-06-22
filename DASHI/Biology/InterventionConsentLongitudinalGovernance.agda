module DASHI.Biology.InterventionConsentLongitudinalGovernance where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

------------------------------------------------------------------------
-- Intervention / consent / longitudinal governance for body-memory.
--
-- This module is candidate-only.  It formalizes a longitudinal governance
-- surface for intervention pacing, consent state transitions, review, and
-- the +1 safety/agency seed.  The seed is not treatment, not cure, and cannot
-- force disclosure.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Route and topology vocabulary.

data GovernanceRoute : Set where
  candidateGovernanceRoute :
    GovernanceRoute

  forcedDisclosureRoute :
    GovernanceRoute

  therapeuticAuthorityRoute :
    GovernanceRoute

  cureClaimRoute :
    GovernanceRoute

  diagnosisRoute :
    GovernanceRoute

  treatmentRoute :
    GovernanceRoute

  clinicalAuthorityRoute :
    GovernanceRoute

  coerciveInstitutionalUseRoute :
    GovernanceRoute

AdmissibleGovernanceRoute :
  GovernanceRoute →
  Set
AdmissibleGovernanceRoute candidateGovernanceRoute = ⊤
AdmissibleGovernanceRoute forcedDisclosureRoute = Never
AdmissibleGovernanceRoute therapeuticAuthorityRoute = Never
AdmissibleGovernanceRoute cureClaimRoute = Never
AdmissibleGovernanceRoute diagnosisRoute = Never
AdmissibleGovernanceRoute treatmentRoute = Never
AdmissibleGovernanceRoute clinicalAuthorityRoute = Never
AdmissibleGovernanceRoute coerciveInstitutionalUseRoute = Never

data Never : Set where

forcedDisclosureRouteRejected :
  AdmissibleGovernanceRoute forcedDisclosureRoute →
  Never
forcedDisclosureRouteRejected impossible = impossible

therapeuticAuthorityRouteRejected :
  AdmissibleGovernanceRoute therapeuticAuthorityRoute →
  Never
therapeuticAuthorityRouteRejected impossible = impossible

cureClaimRouteRejected :
  AdmissibleGovernanceRoute cureClaimRoute →
  Never
cureClaimRouteRejected impossible = impossible

diagnosisRouteRejected :
  AdmissibleGovernanceRoute diagnosisRoute →
  Never
diagnosisRouteRejected impossible = impossible

treatmentRouteRejected :
  AdmissibleGovernanceRoute treatmentRoute →
  Never
treatmentRouteRejected impossible = impossible

clinicalAuthorityRouteRejected :
  AdmissibleGovernanceRoute clinicalAuthorityRoute →
  Never
clinicalAuthorityRouteRejected impossible = impossible

coerciveInstitutionalUseRouteRejected :
  AdmissibleGovernanceRoute coerciveInstitutionalUseRoute →
  Never
coerciveInstitutionalUseRouteRejected impossible = impossible

data TopologyNode : Set where
  chartTopologyNode :
    TopologyNode

  residualTopologyNode :
    TopologyNode

  plusOneTopologyNode :
    TopologyNode

canonicalTopologySignature :
  List TopologyNode
canonicalTopologySignature =
  chartTopologyNode
  ∷ residualTopologyNode
  ∷ plusOneTopologyNode
  ∷ []

canonicalTopologyNodeCount :
  Nat
canonicalTopologyNodeCount =
  listCount canonicalTopologySignature

------------------------------------------------------------------------
-- Consent states and longitudinal gates.

data ConsentState : Set where
  consentRequestedState :
    ConsentState

  consentAffirmedState :
    ConsentState

  consentPausedState :
    ConsentState

  consentStoppedState :
    ConsentState

  consentOrientedState :
    ConsentState

  consentWitnessedState :
    ConsentState

  safetySeedState :
    ConsentState

  consentRevokedState :
    ConsentState

canonicalConsentStates :
  List ConsentState
canonicalConsentStates =
  consentRequestedState
  ∷ consentAffirmedState
  ∷ consentPausedState
  ∷ consentStoppedState
  ∷ consentOrientedState
  ∷ consentWitnessedState
  ∷ safetySeedState
  ∷ consentRevokedState
  ∷ []

canonicalConsentStateCount :
  Nat
canonicalConsentStateCount =
  listCount canonicalConsentStates

data LongitudinalReviewGate : Set where
  pacingGate :
    LongitudinalReviewGate

  stopGate :
    LongitudinalReviewGate

  pauseGate :
    LongitudinalReviewGate

  orientGate :
    LongitudinalReviewGate

  witnessGate :
    LongitudinalReviewGate

  safetyGate :
    LongitudinalReviewGate

  reconsentGate :
    LongitudinalReviewGate

canonicalLongitudinalReviewGates :
  List LongitudinalReviewGate
canonicalLongitudinalReviewGates =
  pacingGate
  ∷ stopGate
  ∷ pauseGate
  ∷ orientGate
  ∷ witnessGate
  ∷ safetyGate
  ∷ reconsentGate
  ∷ []

canonicalLongitudinalReviewGateCount :
  Nat
canonicalLongitudinalReviewGateCount =
  listCount canonicalLongitudinalReviewGates

data GovernanceRowKind : Set where
  stopRowKind :
    GovernanceRowKind

  pauseRowKind :
    GovernanceRowKind

  orientRowKind :
    GovernanceRowKind

  witnessRowKind :
    GovernanceRowKind

  safetyRowKind :
    GovernanceRowKind

  interventionObservationRowKind :
    GovernanceRowKind

  longitudinalReviewRowKind :
    GovernanceRowKind

  safetySeedRowKind :
    GovernanceRowKind

canonicalGovernanceRowKinds :
  List GovernanceRowKind
canonicalGovernanceRowKinds =
  stopRowKind
  ∷ pauseRowKind
  ∷ orientRowKind
  ∷ witnessRowKind
  ∷ safetyRowKind
  ∷ interventionObservationRowKind
  ∷ longitudinalReviewRowKind
  ∷ safetySeedRowKind
  ∷ []

canonicalGovernanceRowKindCount :
  Nat
canonicalGovernanceRowKindCount =
  listCount canonicalGovernanceRowKinds

------------------------------------------------------------------------
-- Concrete governance rows.

record InterventionConsentLongitudinalGovernanceRow : Set where
  constructor mkInterventionConsentLongitudinalGovernanceRow
  field
    rowIndex :
      Nat

    rowKind :
      GovernanceRowKind

    rowConsentState :
      ConsentState

    rowLabel :
      String

    rowSurface :
      String

    rowTopologySignature :
      List TopologyNode

    rowTopologySignatureIsCanonical :
      rowTopologySignature ≡ canonicalTopologySignature

    rowCandidateOnly :
      Bool

    rowCandidateOnlyIsTrue :
      rowCandidateOnly ≡ true

    rowPromoted :
      Bool

    rowPromotedIsFalse :
      rowPromoted ≡ false

    rowForcedDisclosureBlocked :
      Bool

    rowForcedDisclosureBlockedIsTrue :
      rowForcedDisclosureBlocked ≡ true

    rowTherapeuticAuthorityBlocked :
      Bool

    rowTherapeuticAuthorityBlockedIsTrue :
      rowTherapeuticAuthorityBlocked ≡ true

    rowCureClaimBlocked :
      Bool

    rowCureClaimBlockedIsTrue :
      rowCureClaimBlocked ≡ true

    rowDiagnosisBlocked :
      Bool

    rowDiagnosisBlockedIsTrue :
      rowDiagnosisBlocked ≡ true

    rowTreatmentBlocked :
      Bool

    rowTreatmentBlockedIsTrue :
      rowTreatmentBlocked ≡ true

    rowClinicalAuthorityBlocked :
      Bool

    rowClinicalAuthorityBlockedIsTrue :
      rowClinicalAuthorityBlocked ≡ true

    rowCoerciveInstitutionalUseBlocked :
      Bool

    rowCoerciveInstitutionalUseBlockedIsTrue :
      rowCoerciveInstitutionalUseBlocked ≡ true

    rowSafetySeedNotTreatmentOrCure :
      Bool

    rowSafetySeedNotTreatmentOrCureIsTrue :
      rowSafetySeedNotTreatmentOrCure ≡ true

    rowSafetySeedCannotForceDisclosure :
      Bool

    rowSafetySeedCannotForceDisclosureIsTrue :
      rowSafetySeedCannotForceDisclosure ≡ true

    rowClaim :
      String

    rowRemainingGap :
      String

open InterventionConsentLongitudinalGovernanceRow public

record InterventionConsentLongitudinalGovernanceRowCertificate
  (row : InterventionConsentLongitudinalGovernanceRow) :
  Set where
  constructor governanceRowCertificate
  field
    topologySignatureCanonical :
      rowTopologySignature row ≡ canonicalTopologySignature

    candidateOnlyTrue :
      rowCandidateOnly row ≡ true

    promotedFalse :
      rowPromoted row ≡ false

    forcedDisclosureBlockedTrue :
      rowForcedDisclosureBlocked row ≡ true

    therapeuticAuthorityBlockedTrue :
      rowTherapeuticAuthorityBlocked row ≡ true

    cureClaimBlockedTrue :
      rowCureClaimBlocked row ≡ true

    diagnosisBlockedTrue :
      rowDiagnosisBlocked row ≡ true

    treatmentBlockedTrue :
      rowTreatmentBlocked row ≡ true

    clinicalAuthorityBlockedTrue :
      rowClinicalAuthorityBlocked row ≡ true

    coerciveInstitutionalUseBlockedTrue :
      rowCoerciveInstitutionalUseBlocked row ≡ true

    safetySeedNotTreatmentOrCureTrue :
      rowSafetySeedNotTreatmentOrCure row ≡ true

    safetySeedCannotForceDisclosureTrue :
      rowSafetySeedCannotForceDisclosure row ≡ true

open InterventionConsentLongitudinalGovernanceRowCertificate public

canonicalInterventionConsentLongitudinalGovernanceRowCertificate :
  (row : InterventionConsentLongitudinalGovernanceRow) →
  rowTopologySignature row ≡ canonicalTopologySignature →
  rowCandidateOnly row ≡ true →
  rowPromoted row ≡ false →
  rowForcedDisclosureBlocked row ≡ true →
  rowTherapeuticAuthorityBlocked row ≡ true →
  rowCureClaimBlocked row ≡ true →
  rowDiagnosisBlocked row ≡ true →
  rowTreatmentBlocked row ≡ true →
  rowClinicalAuthorityBlocked row ≡ true →
  rowCoerciveInstitutionalUseBlocked row ≡ true →
  rowSafetySeedNotTreatmentOrCure row ≡ true →
  rowSafetySeedCannotForceDisclosure row ≡ true →
  InterventionConsentLongitudinalGovernanceRowCertificate row
canonicalInterventionConsentLongitudinalGovernanceRowCertificate
  row
  topologySignatureCanonical
  candidateOnlyTrue
  promotedFalse
  forcedDisclosureBlockedTrue
  therapeuticAuthorityBlockedTrue
  cureClaimBlockedTrue
  diagnosisBlockedTrue
  treatmentBlockedTrue
  clinicalAuthorityBlockedTrue
  coerciveInstitutionalUseBlockedTrue
  safetySeedNotTreatmentOrCureTrue
  safetySeedCannotForceDisclosureTrue =
  governanceRowCertificate
    topologySignatureCanonical
    candidateOnlyTrue
    promotedFalse
    forcedDisclosureBlockedTrue
    therapeuticAuthorityBlockedTrue
    cureClaimBlockedTrue
    diagnosisBlockedTrue
    treatmentBlockedTrue
    clinicalAuthorityBlockedTrue
    coerciveInstitutionalUseBlockedTrue
    safetySeedNotTreatmentOrCureTrue
    safetySeedCannotForceDisclosureTrue

stopGovernanceRow : InterventionConsentLongitudinalGovernanceRow
stopGovernanceRow =
  mkInterventionConsentLongitudinalGovernanceRow
    zero
    stopRowKind
    consentStoppedState
    "stop governance row"
    "Body-memory intervention stop state with explicit consent hold."
    canonicalTopologySignature
    refl
    true
    refl
    false
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Stopping is a candidate governance action, not therapeutic authority."
    "This row blocks forced disclosure, diagnosis, treatment, cure, clinical authority, and coercive institutional use."

pauseGovernanceRow : InterventionConsentLongitudinalGovernanceRow
pauseGovernanceRow =
  mkInterventionConsentLongitudinalGovernanceRow
    (suc zero)
    pauseRowKind
    consentPausedState
    "pause governance row"
    "Body-memory intervention pause state with paced review."
    canonicalTopologySignature
    refl
    true
    refl
    false
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Pausing is a candidate governance action, not treatment."
    "Pause keeps disclosure voluntary and blocks authority creep."

orientGovernanceRow : InterventionConsentLongitudinalGovernanceRow
orientGovernanceRow =
  mkInterventionConsentLongitudinalGovernanceRow
    (suc (suc zero))
    orientRowKind
    consentOrientedState
    "orient governance row"
    "Orientation state supports situational clarity before any intervention step."
    canonicalTopologySignature
    refl
    true
    refl
    false
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Orientation is a candidate governance action, not diagnosis."
    "This row keeps the +1 safety/agency seed out of cure and treatment claims."

witnessGovernanceRow : InterventionConsentLongitudinalGovernanceRow
witnessGovernanceRow =
  mkInterventionConsentLongitudinalGovernanceRow
    (suc (suc (suc zero)))
    witnessRowKind
    consentWitnessedState
    "witness governance row"
    "Witnessing state records observation without coercive extraction."
    canonicalTopologySignature
    refl
    true
    refl
    false
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Witnessing is a candidate governance action, not compelled disclosure."
    "No witness here can authorize treatment, cure, or institutional coercion."

safetyGovernanceRow : InterventionConsentLongitudinalGovernanceRow
safetyGovernanceRow =
  mkInterventionConsentLongitudinalGovernanceRow
    (suc (suc (suc (suc zero))))
    safetyRowKind
    safetySeedState
    "safety governance row"
    "+1 safety row: agency seed is safeguarded and not repurposed as intervention authority."
    canonicalTopologySignature
    refl
    true
    refl
    false
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "+1 safety/agency seed is not treatment or cure."
    "+1 safety/agency seed cannot force disclosure."

interventionObservationGovernanceRow :
  InterventionConsentLongitudinalGovernanceRow
interventionObservationGovernanceRow =
  mkInterventionConsentLongitudinalGovernanceRow
    (suc (suc (suc (suc (suc zero)))))
    interventionObservationRowKind
    consentAffirmedState
    "intervention observation governance row"
    "Observation row for paced intervention notes, assent, and non-clinical review."
    canonicalTopologySignature
    refl
    true
    refl
    false
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Observation is candidate-only and cannot become treatment authority."
    "Observation stays non-clinical and non-coercive."

longitudinalReviewGovernanceRow :
  InterventionConsentLongitudinalGovernanceRow
longitudinalReviewGovernanceRow =
  mkInterventionConsentLongitudinalGovernanceRow
    (suc (suc (suc (suc (suc (suc zero))))))
    longitudinalReviewRowKind
    consentAffirmedState
    "longitudinal review governance row"
    "Review row for sequencing, pacing, and reconsent across time."
    canonicalTopologySignature
    refl
    true
    refl
    false
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Review is candidate-only governance, not legal or clinical authority."
    "Longitudinal review cannot force disclosure."

safetySeedGovernanceRow :
  InterventionConsentLongitudinalGovernanceRow
safetySeedGovernanceRow =
  mkInterventionConsentLongitudinalGovernanceRow
    (suc (suc (suc (suc (suc (suc (suc zero)))))))
    safetySeedRowKind
    safetySeedState
    "safety seed governance row"
    "+1 safety/agency seed row for body-memory pacing and reconsent support."
    canonicalTopologySignature
    refl
    true
    refl
    false
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "+1 safety/agency seed is a governance seed, not treatment or cure."
    "+1 safety/agency seed cannot force disclosure."

canonicalGovernanceRows :
  List InterventionConsentLongitudinalGovernanceRow
canonicalGovernanceRows =
  stopGovernanceRow
  ∷ pauseGovernanceRow
  ∷ orientGovernanceRow
  ∷ witnessGovernanceRow
  ∷ safetyGovernanceRow
  ∷ interventionObservationGovernanceRow
  ∷ longitudinalReviewGovernanceRow
  ∷ safetySeedGovernanceRow
  ∷ []

canonicalGovernanceRowCount :
  Nat
canonicalGovernanceRowCount =
  listCount canonicalGovernanceRows

canonicalStopGovernanceRowCertificate :
  InterventionConsentLongitudinalGovernanceRowCertificate stopGovernanceRow
canonicalStopGovernanceRowCertificate =
  canonicalInterventionConsentLongitudinalGovernanceRowCertificate
    stopGovernanceRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalPauseGovernanceRowCertificate :
  InterventionConsentLongitudinalGovernanceRowCertificate pauseGovernanceRow
canonicalPauseGovernanceRowCertificate =
  canonicalInterventionConsentLongitudinalGovernanceRowCertificate
    pauseGovernanceRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalOrientGovernanceRowCertificate :
  InterventionConsentLongitudinalGovernanceRowCertificate orientGovernanceRow
canonicalOrientGovernanceRowCertificate =
  canonicalInterventionConsentLongitudinalGovernanceRowCertificate
    orientGovernanceRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalWitnessGovernanceRowCertificate :
  InterventionConsentLongitudinalGovernanceRowCertificate witnessGovernanceRow
canonicalWitnessGovernanceRowCertificate =
  canonicalInterventionConsentLongitudinalGovernanceRowCertificate
    witnessGovernanceRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalSafetyGovernanceRowCertificate :
  InterventionConsentLongitudinalGovernanceRowCertificate safetyGovernanceRow
canonicalSafetyGovernanceRowCertificate =
  canonicalInterventionConsentLongitudinalGovernanceRowCertificate
    safetyGovernanceRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalInterventionObservationGovernanceRowCertificate :
  InterventionConsentLongitudinalGovernanceRowCertificate
    interventionObservationGovernanceRow
canonicalInterventionObservationGovernanceRowCertificate =
  canonicalInterventionConsentLongitudinalGovernanceRowCertificate
    interventionObservationGovernanceRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalLongitudinalReviewGovernanceRowCertificate :
  InterventionConsentLongitudinalGovernanceRowCertificate
    longitudinalReviewGovernanceRow
canonicalLongitudinalReviewGovernanceRowCertificate =
  canonicalInterventionConsentLongitudinalGovernanceRowCertificate
    longitudinalReviewGovernanceRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

canonicalSafetySeedGovernanceRowCertificate :
  InterventionConsentLongitudinalGovernanceRowCertificate safetySeedGovernanceRow
canonicalSafetySeedGovernanceRowCertificate =
  canonicalInterventionConsentLongitudinalGovernanceRowCertificate
    safetySeedGovernanceRow
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl
    refl

------------------------------------------------------------------------
-- Canonical record.

record InterventionConsentLongitudinalGovernance : Set where
  constructor mkInterventionConsentLongitudinalGovernance
  field
    governanceRoute :
      GovernanceRoute

    governanceRouteIsCandidate :
      governanceRoute ≡ candidateGovernanceRoute

    governanceRouteAdmissible :
      AdmissibleGovernanceRoute governanceRoute

    consentStates :
      List ConsentState

    consentStatesAreCanonical :
      consentStates ≡ canonicalConsentStates

    reviewGates :
      List LongitudinalReviewGate

    reviewGatesAreCanonical :
      reviewGates ≡ canonicalLongitudinalReviewGates

    governanceRows :
      List InterventionConsentLongitudinalGovernanceRow

    governanceRowsAreCanonical :
      governanceRows ≡ canonicalGovernanceRows

    stopRowCertificate :
      InterventionConsentLongitudinalGovernanceRowCertificate stopGovernanceRow

    pauseRowCertificate :
      InterventionConsentLongitudinalGovernanceRowCertificate pauseGovernanceRow

    orientRowCertificate :
      InterventionConsentLongitudinalGovernanceRowCertificate orientGovernanceRow

    witnessRowCertificate :
      InterventionConsentLongitudinalGovernanceRowCertificate witnessGovernanceRow

    safetyRowCertificate :
      InterventionConsentLongitudinalGovernanceRowCertificate safetyGovernanceRow

    interventionObservationRowCertificate :
      InterventionConsentLongitudinalGovernanceRowCertificate
        interventionObservationGovernanceRow

    longitudinalReviewRowCertificate :
      InterventionConsentLongitudinalGovernanceRowCertificate
        longitudinalReviewGovernanceRow

    safetySeedRowCertificate :
      InterventionConsentLongitudinalGovernanceRowCertificate
        safetySeedGovernanceRow

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    forcedDisclosureBlocked :
      Bool

    forcedDisclosureBlockedIsTrue :
      forcedDisclosureBlocked ≡ true

    therapeuticAuthorityBlocked :
      Bool

    therapeuticAuthorityBlockedIsTrue :
      therapeuticAuthorityBlocked ≡ true

    cureClaimBlocked :
      Bool

    cureClaimBlockedIsTrue :
      cureClaimBlocked ≡ true

    diagnosisBlocked :
      Bool

    diagnosisBlockedIsTrue :
      diagnosisBlocked ≡ true

    treatmentBlocked :
      Bool

    treatmentBlockedIsTrue :
      treatmentBlocked ≡ true

    clinicalAuthorityBlocked :
      Bool

    clinicalAuthorityBlockedIsTrue :
      clinicalAuthorityBlocked ≡ true

    coerciveInstitutionalUseBlocked :
      Bool

    coerciveInstitutionalUseBlockedIsTrue :
      coerciveInstitutionalUseBlocked ≡ true

    safetySeedNotTreatmentOrCure :
      Bool

    safetySeedNotTreatmentOrCureIsTrue :
      safetySeedNotTreatmentOrCure ≡ true

    safetySeedCannotForceDisclosure :
      Bool

    safetySeedCannotForceDisclosureIsTrue :
      safetySeedCannotForceDisclosure ≡ true

    governanceReading :
      String

open InterventionConsentLongitudinalGovernance public

canonicalInterventionConsentLongitudinalGovernance :
  InterventionConsentLongitudinalGovernance
canonicalInterventionConsentLongitudinalGovernance =
  mkInterventionConsentLongitudinalGovernance
    candidateGovernanceRoute
    refl
    tt
    canonicalConsentStates
    refl
    canonicalLongitudinalReviewGates
    refl
    canonicalGovernanceRows
    refl
    canonicalStopGovernanceRowCertificate
    canonicalPauseGovernanceRowCertificate
    canonicalOrientGovernanceRowCertificate
    canonicalWitnessGovernanceRowCertificate
    canonicalSafetyGovernanceRowCertificate
    canonicalInterventionObservationGovernanceRowCertificate
    canonicalLongitudinalReviewGovernanceRowCertificate
    canonicalSafetySeedGovernanceRowCertificate
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    true
    refl
    "Candidate-only longitudinal governance for body-memory intervention pacing, consent, review, and +1 safety/agency seed protection."

canonicalGovernanceRouteIsCandidate :
  governanceRoute canonicalInterventionConsentLongitudinalGovernance
  ≡
  candidateGovernanceRoute
canonicalGovernanceRouteIsCandidate =
  governanceRouteIsCandidate canonicalInterventionConsentLongitudinalGovernance

canonicalCandidateOnlyTrue :
  candidateOnly canonicalInterventionConsentLongitudinalGovernance ≡ true
canonicalCandidateOnlyTrue =
  candidateOnlyIsTrue canonicalInterventionConsentLongitudinalGovernance

canonicalForcedDisclosureBlockedTrue :
  forcedDisclosureBlocked canonicalInterventionConsentLongitudinalGovernance ≡ true
canonicalForcedDisclosureBlockedTrue =
  forcedDisclosureBlockedIsTrue canonicalInterventionConsentLongitudinalGovernance

canonicalTherapeuticAuthorityBlockedTrue :
  therapeuticAuthorityBlocked canonicalInterventionConsentLongitudinalGovernance ≡ true
canonicalTherapeuticAuthorityBlockedTrue =
  therapeuticAuthorityBlockedIsTrue canonicalInterventionConsentLongitudinalGovernance

canonicalCureClaimBlockedTrue :
  cureClaimBlocked canonicalInterventionConsentLongitudinalGovernance ≡ true
canonicalCureClaimBlockedTrue =
  cureClaimBlockedIsTrue canonicalInterventionConsentLongitudinalGovernance

canonicalDiagnosisBlockedTrue :
  diagnosisBlocked canonicalInterventionConsentLongitudinalGovernance ≡ true
canonicalDiagnosisBlockedTrue =
  diagnosisBlockedIsTrue canonicalInterventionConsentLongitudinalGovernance

canonicalTreatmentBlockedTrue :
  treatmentBlocked canonicalInterventionConsentLongitudinalGovernance ≡ true
canonicalTreatmentBlockedTrue =
  treatmentBlockedIsTrue canonicalInterventionConsentLongitudinalGovernance

canonicalClinicalAuthorityBlockedTrue :
  clinicalAuthorityBlocked canonicalInterventionConsentLongitudinalGovernance ≡ true
canonicalClinicalAuthorityBlockedTrue =
  clinicalAuthorityBlockedIsTrue canonicalInterventionConsentLongitudinalGovernance

canonicalCoerciveInstitutionalUseBlockedTrue :
  coerciveInstitutionalUseBlocked
    canonicalInterventionConsentLongitudinalGovernance
  ≡
  true
canonicalCoerciveInstitutionalUseBlockedTrue =
  coerciveInstitutionalUseBlockedIsTrue
    canonicalInterventionConsentLongitudinalGovernance

canonicalSafetySeedNotTreatmentOrCureTrue :
  safetySeedNotTreatmentOrCure
    canonicalInterventionConsentLongitudinalGovernance
  ≡
  true
canonicalSafetySeedNotTreatmentOrCureTrue =
  safetySeedNotTreatmentOrCureIsTrue
    canonicalInterventionConsentLongitudinalGovernance

canonicalSafetySeedCannotForceDisclosureTrue :
  safetySeedCannotForceDisclosure
    canonicalInterventionConsentLongitudinalGovernance
  ≡
  true
canonicalSafetySeedCannotForceDisclosureTrue =
  safetySeedCannotForceDisclosureIsTrue
    canonicalInterventionConsentLongitudinalGovernance

canonicalLongitudinalReviewGateCountIsCanonical :
  canonicalLongitudinalReviewGateCount ≡ suc (suc (suc (suc (suc (suc (suc zero)))))) 
canonicalLongitudinalReviewGateCountIsCanonical =
  refl

