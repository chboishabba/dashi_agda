module DASHI.Planning.IrreversibleActionConsentReopeningGateExact where

open import DASHI.Core.Prelude
import DASHI.Planning.CollectiveTerritorialConsentExact as Consent

------------------------------------------------------------------------
-- IRREVERSIBLE ACTION CONSENT / REOPENING GATE
------------------------------------------------------------------------

data ImpactKind : Set where
  reversibleImpact irreversibleNonSubstitutableImpact : ImpactKind

data MaterialEvidenceState : Set where
  currentEvidence materiallyChangedEvidence : MaterialEvidenceState

record IrreversibleActionGate
    (envelope : Consent.CollectiveConsentEnvelope)
    (evidence : MaterialEvidenceState) : Set where
  constructor irreversibleActionGate
  field
    consentCurrent : Consent.CollectiveConsentEnvelope.stage envelope ≡ Consent.consentGiven
    refusalPowerPresent :
      Consent.CollectiveConsentEnvelope.contestability envelope ≡ Consent.canWithdraw
    informationCurrent :
      Consent.CollectiveConsentEnvelope.informationMateriallyCurrent envelope ≡ true
    reopenable :
      Consent.CollectiveConsentEnvelope.reopeningOnMaterialChange envelope ≡ true
    evidenceStillCurrent : evidence ≡ currentEvidence

open IrreversibleActionGate public

canonicalIrreversibleGate :
  IrreversibleActionGate Consent.withdrawableConsent currentEvidence
canonicalIrreversibleGate = irreversibleActionGate refl refl refl refl refl

consultationOnlyCannotGateIrreversibleAction :
  IrreversibleActionGate Consent.consultationOnly currentEvidence → ⊥
consultationOnlyCannotGateIrreversibleAction gate =
  Consent.consultedIsNotConsentGiven (consentCurrent gate)

materialChangeReopensIrreversibleDecision :
  IrreversibleActionGate Consent.withdrawableConsent materiallyChangedEvidence → ⊥
materialChangeReopensIrreversibleDecision gate with evidenceStillCurrent gate
... | ()

record IrreversibleActionBoundary : Set where
  constructor irreversibleActionBoundary
  field
    historicalApprovalSurvivesMaterialChangeAutomatically : Bool
    historicalApprovalSurvivesMaterialChangeAutomaticallyIsFalse :
      historicalApprovalSurvivesMaterialChangeAutomatically ≡ false
    consultationAloneGatesIrreversibleAction : Bool
    consultationAloneGatesIrreversibleActionIsFalse :
      consultationAloneGatesIrreversibleAction ≡ false

canonicalIrreversibleActionBoundary : IrreversibleActionBoundary
canonicalIrreversibleActionBoundary = irreversibleActionBoundary false refl false refl
