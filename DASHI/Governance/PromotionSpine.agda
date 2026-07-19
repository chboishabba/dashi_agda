module DASHI.Governance.PromotionSpine where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.CandidateOnlyCore as Candidate
import DASHI.Core.GenericReceipt as Generic
import DASHI.Foundations.CanonicalProvenancePromotion as Canonical
import DASHI.Governance.GovernedArtifactCore as Governed

------------------------------------------------------------------------
-- Shared diagnostic and authorization spine.
--
-- The repository has four deliberately distinct surfaces:
--
--   * CandidateOnlyCore records that a row has no local authority.
--   * GenericReceipt records non-promoting audit metadata.
--   * CanonicalProvenancePromotion owns closure obligations and quarantine.
--   * GovernedArtifactCore owns the only state-selection constructors.
--
-- This module makes those surfaces compose without identifying them.

diagnosticFromSeverity :
  Canonical.Severity →
  Governed.DiagnosticSeverity
diagnosticFromSeverity Canonical.informational =
  Governed.pass
diagnosticFromSeverity Canonical.warning =
  Governed.warn
diagnosticFromSeverity Canonical.blocking =
  Governed.fail
diagnosticFromSeverity Canonical.inconsistent =
  Governed.fail

diagnosticFromResidual :
  Canonical.Residual →
  Governed.DiagnosticSeverity
diagnosticFromResidual residual =
  diagnosticFromSeverity (Canonical.severity residual)

exactResidualPasses :
  diagnosticFromResidual Canonical.exact ≡ Governed.pass
exactResidualPasses =
  refl

partialResidualWarns :
  diagnosticFromResidual Canonical.partial ≡ Governed.warn
partialResidualWarns =
  refl

noTypedMeetFails :
  diagnosticFromResidual Canonical.noTypedMeet ≡ Governed.fail
noTypedMeetFails =
  refl

contradictionFails :
  diagnosticFromResidual Canonical.contradiction ≡ Governed.fail
contradictionFails =
  refl

decisionFromPromotionStatus :
  Canonical.PromotionStatus →
  Governed.Decision
decisionFromPromotionStatus Canonical.promoted =
  Governed.promote
decisionFromPromotionStatus Canonical.rejectedStatus =
  Governed.reject
decisionFromPromotionStatus _ =
  Governed.abstain

authorizationFromObligations :
  Canonical.PromotionObligations →
  Governed.Decision
authorizationFromObligations obligations
  with Canonical.allClosed obligations
... | true =
  Governed.promote
... | false =
  Governed.abstain

authorizationAgreesWithCanonicalPromotion :
  (obligations : Canonical.PromotionObligations) →
  authorizationFromObligations obligations
    ≡ decisionFromPromotionStatus (Canonical.promote obligations)
authorizationAgreesWithCanonicalPromotion obligations
  with Canonical.allClosed obligations
... | true =
  refl
... | false =
  refl

fullyClosedAuthorizesPromotion :
  authorizationFromObligations
    (Canonical.promotionObligations true true true true true)
    ≡ Governed.promote
fullyClosedAuthorizesPromotion =
  refl

missingCanonicalIdentityAbstains :
  authorizationFromObligations
    (Canonical.promotionObligations false true true true true)
    ≡ Governed.abstain
missingCanonicalIdentityAbstains =
  refl

missingAdmissibilityAbstains :
  authorizationFromObligations
    (Canonical.promotionObligations true false true true true)
    ≡ Governed.abstain
missingAdmissibilityAbstains =
  refl

missingResidualClosureAbstains :
  authorizationFromObligations
    (Canonical.promotionObligations true true false true true)
    ≡ Governed.abstain
missingResidualClosureAbstains =
  refl

missingWitnessClosureAbstains :
  authorizationFromObligations
    (Canonical.promotionObligations true true true false true)
    ≡ Governed.abstain
missingWitnessClosureAbstains =
  refl

missingValidationAbstains :
  authorizationFromObligations
    (Canonical.promotionObligations true true true true false)
    ≡ Governed.abstain
missingValidationAbstains =
  refl

------------------------------------------------------------------------
-- Candidate-only and generic receipt adapters.

candidateOnlyObligations :
  ∀ {row : Candidate.CandidateOnlyRow} →
  Candidate.CandidateOnlyReceipt row →
  Bool →
  Bool →
  Bool →
  Bool →
  Canonical.PromotionObligations
candidateOnlyObligations
  receipt
  canonicalIdentity
  residualClosure
  witnessClosure
  validationClosure
  with Candidate.candidateNoAdmissibilityAuthority receipt
... | refl =
  Canonical.promotionObligations
    canonicalIdentity
    false
    residualClosure
    witnessClosure
    validationClosure

candidateOnlyQuarantines :
  ∀ {row : Candidate.CandidateOnlyRow} →
  (receipt : Candidate.CandidateOnlyReceipt row) →
  (canonicalIdentity residualClosure witnessClosure validationClosure : Bool) →
  Canonical.promote
    (candidateOnlyObligations
      receipt
      canonicalIdentity
      residualClosure
      witnessClosure
      validationClosure)
    ≡ Canonical.quarantinedStatus
candidateOnlyQuarantines
  receipt
  canonicalIdentity
  residualClosure
  witnessClosure
  validationClosure
  with Candidate.candidateNoAdmissibilityAuthority receipt
... | refl =
  refl

candidateOnlyAuthorizationAbstains :
  ∀ {row : Candidate.CandidateOnlyRow} →
  (receipt : Candidate.CandidateOnlyReceipt row) →
  (canonicalIdentity residualClosure witnessClosure validationClosure : Bool) →
  authorizationFromObligations
    (candidateOnlyObligations
      receipt
      canonicalIdentity
      residualClosure
      witnessClosure
      validationClosure)
    ≡ Governed.abstain
candidateOnlyAuthorizationAbstains
  receipt
  canonicalIdentity
  residualClosure
  witnessClosure
  validationClosure
  with Candidate.candidateNoAdmissibilityAuthority receipt
... | refl =
  refl

genericReceiptToCanonical :
  Generic.GenericReceipt →
  List Canonical.CID →
  List Canonical.CID →
  Canonical.CID →
  Canonical.Receipt
genericReceiptToCanonical receipt inputs outputs trace =
  Canonical.receipt
    inputs
    (Generic.receiptSurface receipt)
    (Generic.receiptOwner receipt
      ∷ Generic.validationCommand receipt
      ∷ [])
    outputs
    trace
    (Generic.receiptRemainingGap receipt ∷ [])
    Canonical.quarantined

genericReceiptRemainsQuarantined :
  (receipt : Generic.GenericReceipt) →
  (inputs outputs : List Canonical.CID) →
  (trace : Canonical.CID) →
  Canonical.Receipt.status
    (genericReceiptToCanonical receipt inputs outputs trace)
    ≡ Canonical.quarantined
genericReceiptRemainsQuarantined receipt inputs outputs trace =
  refl

------------------------------------------------------------------------
-- Closure obligations now drive the only canonical state-selection surface.

governedOutcomeFromObligations :
  ∀ {State Policy Evidence Hash Warning Blocker : Set} →
  (envelope : Governed.CandidateEnvelope State Policy Evidence Hash) →
  (obligations : Canonical.PromotionObligations) →
  Governed.DiagnosticSeverity →
  List Warning →
  List Blocker →
  Hash →
  Hash →
  Governed.GovernedOutcome
    State Policy Evidence Hash Warning Blocker
    (Governed.inputState envelope)
    (Governed.candidateState envelope)
governedOutcomeFromObligations
  envelope
  obligations
  severity
  warnings
  blockers
  policyHash
  receiptHash
  with Canonical.allClosed obligations
... | true =
  Governed.governedOutcome
    (Governed.receipt
      envelope
      severity
      warnings
      blockers
      Governed.promote
      policyHash
      receiptHash)
    (Governed.candidateState envelope)
    (Governed.promoteSelected refl)
... | false =
  Governed.governedOutcome
    (Governed.receipt
      envelope
      severity
      warnings
      blockers
      Governed.abstain
      policyHash
      receiptHash)
    (Governed.inputState envelope)
    (Governed.abstainSelected refl)

fullyClosedOutcomeSelectsCandidate :
  ∀ {State Policy Evidence Hash Warning Blocker : Set}
    (envelope : Governed.CandidateEnvelope State Policy Evidence Hash)
    (severity : Governed.DiagnosticSeverity)
    (warnings : List Warning)
    (blockers : List Blocker)
    (policyHash receiptHash : Hash) →
  Governed.resultState
    (governedOutcomeFromObligations
      envelope
      (Canonical.promotionObligations true true true true true)
      severity
      warnings
      blockers
      policyHash
      receiptHash)
    ≡ Governed.candidateState envelope
fullyClosedOutcomeSelectsCandidate
  envelope
  severity
  warnings
  blockers
  policyHash
  receiptHash =
  refl

candidateOnlyOutcomePreservesInput :
  ∀ {State Policy Evidence Hash Warning Blocker : Set}
    {row : Candidate.CandidateOnlyRow}
    (candidateReceipt : Candidate.CandidateOnlyReceipt row)
    (envelope : Governed.CandidateEnvelope State Policy Evidence Hash)
    (canonicalIdentity residualClosure witnessClosure validationClosure : Bool)
    (severity : Governed.DiagnosticSeverity)
    (warnings : List Warning)
    (blockers : List Blocker)
    (policyHash receiptHash : Hash) →
  Governed.resultState
    (governedOutcomeFromObligations
      envelope
      (candidateOnlyObligations
        candidateReceipt
        canonicalIdentity
        residualClosure
        witnessClosure
        validationClosure)
      severity
      warnings
      blockers
      policyHash
      receiptHash)
    ≡ Governed.inputState envelope
candidateOnlyOutcomePreservesInput
  candidateReceipt
  envelope
  canonicalIdentity
  residualClosure
  witnessClosure
  validationClosure
  severity
  warnings
  blockers
  policyHash
  receiptHash
  with Candidate.candidateNoAdmissibilityAuthority candidateReceipt
... | refl =
  refl
