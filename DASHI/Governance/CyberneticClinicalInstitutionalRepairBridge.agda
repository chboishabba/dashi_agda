module DASHI.Governance.CyberneticClinicalInstitutionalRepairBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Cybernetic / clinical / institutional repair bridge.
--
-- This module gives the governance side of the current DASHI formalism:
-- feedback architecture, System 5, clinical gates, medical-cannabis driving
-- presence/impairment separation, and institutional repair continuity.
--
-- It is candidate-only.  It does not assert legal advice, clinical advice,
-- a finding of discrimination, impairment status, or liability.  It only
-- records the shape of the gates and the non-promotion guards.

listCount : ∀ {A : Set} → List A → Nat
listCount [] =
  zero
listCount (_ ∷ xs) =
  suc (listCount xs)

------------------------------------------------------------------------
-- Governance domains.

data GovernanceDomain : Set where
  cybersynSystemFiveDomain :
    GovernanceDomain

  educationFeedbackDomain :
    GovernanceDomain

  transHealthcareGateDomain :
    GovernanceDomain

  medicalCannabisDrivingDomain :
    GovernanceDomain

  institutionalRepairDomain :
    GovernanceDomain

canonicalGovernanceDomains :
  List GovernanceDomain
canonicalGovernanceDomains =
  cybersynSystemFiveDomain
  ∷ educationFeedbackDomain
  ∷ transHealthcareGateDomain
  ∷ medicalCannabisDrivingDomain
  ∷ institutionalRepairDomain
  ∷ []

canonicalGovernanceDomainCount : Nat
canonicalGovernanceDomainCount =
  listCount canonicalGovernanceDomains

------------------------------------------------------------------------
-- Gate rows.

record GovernanceGateRow : Set where
  constructor mkGovernanceGateRow
  field
    rowIndex :
      Nat

    rowDomain :
      GovernanceDomain

    rowLabel :
      String

    rowClaim :
      String

    feedbackSubjectRestored :
      Bool

    feedbackSubjectRestoredIsTrue :
      feedbackSubjectRestored ≡ true

    gateAsHarmTracked :
      Bool

    gateAsHarmTrackedIsTrue :
      gateAsHarmTracked ≡ true

    candidateOnly :
      Bool

    candidateOnlyIsTrue :
      candidateOnly ≡ true

    legalAuthorityPromoted :
      Bool

    legalAuthorityPromotedIsFalse :
      legalAuthorityPromoted ≡ false

    clinicalAuthorityPromoted :
      Bool

    clinicalAuthorityPromotedIsFalse :
      clinicalAuthorityPromoted ≡ false

    impairmentFindingPromoted :
      Bool

    impairmentFindingPromotedIsFalse :
      impairmentFindingPromoted ≡ false

    liabilityFindingPromoted :
      Bool

    liabilityFindingPromotedIsFalse :
      liabilityFindingPromoted ≡ false

    remainingGap :
      String

open GovernanceGateRow public

mkCanonicalGateRow :
  Nat →
  GovernanceDomain →
  String →
  String →
  String →
  GovernanceGateRow
mkCanonicalGateRow index domain label claim gap =
  mkGovernanceGateRow
    index
    domain
    label
    claim
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    gap

cybersynSystemFiveRow : GovernanceGateRow
cybersynSystemFiveRow =
  mkCanonicalGateRow
    zero
    cybersynSystemFiveDomain
    "system-five-is-the-people"
    "A cybernetic governance loop is legitimate only when the affected people can steer the highest identity/reference layer."
    "This row does not prove any particular institutional design sufficient."

educationFeedbackRow : GovernanceGateRow
educationFeedbackRow =
  mkCanonicalGateRow
    (suc zero)
    educationFeedbackDomain
    "education-feedback-not-surveillance"
    "Voice, agency, situated ethics, partnership, enactment, engagement intelligence, and equity are treated as feedback gates."
    "This row does not promote metrics, surveys, attendance, or clicks as sovereign evidence of learning."

transHealthcareGateRow : GovernanceGateRow
transHealthcareGateRow =
  mkCanonicalGateRow
    (suc (suc zero))
    transHealthcareGateDomain
    "clinical-pathway-gate-can-be-the-harm"
    "A restriction can target access to assessment / pathway entry before any final treatment outcome is known."
    "This row records a procedural shape only; it is not a legal finding on any live dispute."

medicalCannabisDrivingRow : GovernanceGateRow
medicalCannabisDrivingRow =
  mkCanonicalGateRow
    (suc (suc (suc zero)))
    medicalCannabisDrivingDomain
    "presence-is-not-impairment"
    "THC presence, prescription status, chronic tolerance, and functional impairment are distinct governance coordinates."
    "This row gives no driving advice and makes no impairment finding."

institutionalRepairRow : GovernanceGateRow
institutionalRepairRow =
  mkCanonicalGateRow
    (suc (suc (suc (suc zero))))
    institutionalRepairDomain
    "mission-flow-requires-repair-flow"
    "If mission, assets, subsidy, tax privilege, and public legitimacy flow forward, survivor repair must not be stranded in a depleted shell."
    "This row is a repair-continuity gate, not a court finding or liability determination."

canonicalGovernanceGateRows :
  List GovernanceGateRow
canonicalGovernanceGateRows =
  cybersynSystemFiveRow
  ∷ educationFeedbackRow
  ∷ transHealthcareGateRow
  ∷ medicalCannabisDrivingRow
  ∷ institutionalRepairRow
  ∷ []

canonicalGovernanceGateRowCount : Nat
canonicalGovernanceGateRowCount =
  listCount canonicalGovernanceGateRows

------------------------------------------------------------------------
-- Governance receipt.

record CyberneticClinicalInstitutionalRepairBridge : Set where
  constructor mkCyberneticClinicalInstitutionalRepairBridge
  field
    bridgeDomains :
      List GovernanceDomain

    bridgeDomainsAreCanonical :
      bridgeDomains ≡ canonicalGovernanceDomains

    gateRows :
      List GovernanceGateRow

    gateRowsAreCanonical :
      gateRows ≡ canonicalGovernanceGateRows

    systemFivePeopleRequired :
      Bool

    systemFivePeopleRequiredIsTrue :
      systemFivePeopleRequired ≡ true

    feedbackAsSurveillanceBlocked :
      Bool

    feedbackAsSurveillanceBlockedIsTrue :
      feedbackAsSurveillanceBlocked ≡ true

    clinicalGateAsHarmTracked :
      Bool

    clinicalGateAsHarmTrackedIsTrue :
      clinicalGateAsHarmTracked ≡ true

    presenceEqualsImpairmentPromoted :
      Bool

    presenceEqualsImpairmentPromotedIsFalse :
      presenceEqualsImpairmentPromoted ≡ false

    missionShieldPromotion :
      Bool

    missionShieldPromotionIsFalse :
      missionShieldPromotion ≡ false

    legalAdvicePromoted :
      Bool

    legalAdvicePromotedIsFalse :
      legalAdvicePromoted ≡ false

    clinicalAdvicePromoted :
      Bool

    clinicalAdvicePromotedIsFalse :
      clinicalAdvicePromoted ≡ false

    bridgeReading :
      String

open CyberneticClinicalInstitutionalRepairBridge public

canonicalCyberneticClinicalInstitutionalRepairBridge :
  CyberneticClinicalInstitutionalRepairBridge
canonicalCyberneticClinicalInstitutionalRepairBridge =
  mkCyberneticClinicalInstitutionalRepairBridge
    canonicalGovernanceDomains
    refl
    canonicalGovernanceGateRows
    refl
    true
    refl
    true
    refl
    true
    refl
    false
    refl
    false
    refl
    false
    refl
    false
    refl
    "Governance is modeled as feedback architecture: System 5 must be the people; gates can be harms; presence is not impairment; mission continuity cannot shield repair discontinuity."

canonicalPresenceEqualsImpairmentPromotedFalse :
  presenceEqualsImpairmentPromoted canonicalCyberneticClinicalInstitutionalRepairBridge ≡ false
canonicalPresenceEqualsImpairmentPromotedFalse =
  presenceEqualsImpairmentPromotedIsFalse canonicalCyberneticClinicalInstitutionalRepairBridge

canonicalMissionShieldPromotionFalse :
  missionShieldPromotion canonicalCyberneticClinicalInstitutionalRepairBridge ≡ false
canonicalMissionShieldPromotionFalse =
  missionShieldPromotionIsFalse canonicalCyberneticClinicalInstitutionalRepairBridge

canonicalLegalAdvicePromotedFalse :
  legalAdvicePromoted canonicalCyberneticClinicalInstitutionalRepairBridge ≡ false
canonicalLegalAdvicePromotedFalse =
  legalAdvicePromotedIsFalse canonicalCyberneticClinicalInstitutionalRepairBridge

canonicalClinicalAdvicePromotedFalse :
  clinicalAdvicePromoted canonicalCyberneticClinicalInstitutionalRepairBridge ≡ false
canonicalClinicalAdvicePromotedFalse =
  clinicalAdvicePromotedIsFalse canonicalCyberneticClinicalInstitutionalRepairBridge
